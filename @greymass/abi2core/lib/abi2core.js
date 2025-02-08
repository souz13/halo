#!/usr/bin/env node

/**
 * @greymass/abi2core v1.1.0
 * https://github.com/greymass/abi2core
 *
 * @license
 * Copyright (c) 2021 FFF00 Agents AB & Greymass Inc. All Rights Reserved.
 * 
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 * 
 *  1. Redistribution of source code must retain the above copyright notice, this
 *     list of conditions and the following disclaimer.
 * 
 *  2. Redistribution in binary form must reproduce the above copyright notice,
 *     this list of conditions and the following disclaimer in the documentation
 *     and/or other materials provided with the distribution.
 * 
 *  3. Neither the name of the copyright holder nor the names of its contributors
 *     may be used to endorse or promote products derived from this software without
 *     specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
 * OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * YOU ACKNOWLEDGE THAT THIS SOFTWARE IS NOT DESIGNED, LICENSED OR INTENDED FOR USE
 * IN THE DESIGN, CONSTRUCTION, OPERATION OR MAINTENANCE OF ANY MILITARY FACILITY.
 */
'use strict';

Object.defineProperty(exports, '__esModule', { value: true });

var tslib = require('tslib');
var argparse = require('argparse');
var fs = require('fs');
var eosio = require('@greymass/eosio');

// adapted from https://github.com/gustavohenke/toposort
class Toposort {
    constructor() {
        this.edges = [];
    }
    add(item, deps) {
        deps = Array.isArray(deps) ? deps : [deps];
        if (deps.length > 0) {
            for (const dep of deps) {
                this.edges.push([item, dep]);
            }
        }
        else {
            this.edges.push([item]);
        }
    }
    sort() {
        const nodes = [];
        for (const edge of this.edges) {
            for (const node of edge) {
                if (nodes.indexOf(node) === -1) {
                    nodes.push(node);
                }
            }
        }
        let place = nodes.length;
        const sorted = new Array(nodes.length);
        const visit = (node, predecessors) => {
            if (predecessors.length !== 0 && predecessors.indexOf(node) !== -1) {
                throw new Error(`Cyclic dependency found. ${node} is dependent of itself.\n` +
                    `Dependency chain: ${predecessors.join(' -> ')} => ${node}`);
            }
            const index = nodes.indexOf(node);
            if (index !== -1) {
                let copy = false;
                nodes[index] = false;
                for (const edge of this.edges) {
                    if (edge[0] === node) {
                        copy = copy || predecessors.concat([node]);
                        visit(edge[1], copy);
                    }
                }
                sorted[--place] = node;
            }
        };
        for (let i = 0; i < nodes.length; i++) {
            const node = nodes[i];
            if (node !== false) {
                nodes[i] = false;
                for (const edge of this.edges) {
                    if (edge[0] === node) {
                        visit(edge[1], [node]);
                    }
                }
                sorted[--place] = node;
            }
        }
        return sorted;
    }
}

function transform(abiDef) {
    const abi = eosio.ABI.from(abiDef);
    const out = [''];
    const resolved = abi.resolveAll();
    const imports = new Set();
    if (resolved.structs.length > 0) {
        imports.add('Struct');
    }
    if (resolved.types.length > 0) {
        imports.add('TypeAlias');
    }
    if (resolved.variants.length > 0) {
        imports.add('Variant');
    }
    const typeGraph = new Toposort();
    resolved.types.forEach((type) => {
        typeGraph.add(type.name, type.ref.name);
    });
    resolved.structs.forEach((type) => {
        typeGraph.add(type.name, type.fields.map((f) => f.type.name));
    });
    resolved.variants.forEach((type) => {
        typeGraph.add(type.name, type.variant.map((t) => t.name));
    });
    const typeOrder = typeGraph.sort().reverse();
    const allTypes = resolved.structs
        .concat(resolved.variants)
        .concat(resolved.types)
        .sort((a, b) => {
        return typeOrder.indexOf(a.name) - typeOrder.indexOf(b.name);
    });
    const getTypeName = (type) => {
        const builtin = getBuiltin(type);
        if (builtin) {
            if (allTypes.find((t) => t.name === type.name)) {
                process.stderr.write(`WARNING: ABI re-declares builtin: "${type.name}". This will result in undefined behavior.\n`);
            }
            else {
                imports.add(builtin.import);
            }
        }
        return builtin ? builtin.name : snakeToPascal(sanitizeTypeName(type.name));
    };
    for (const type of allTypes) {
        if (type.ref) {
            if (type.ref.name === 'string' || type.ref.name === 'bool') {
                throw new Error('@greymass/eosio can not represent aliases to types represented by js natives (string and bool)');
            }
            const baseType = getTypeName(type.ref);
            out.push(`@TypeAlias('${type.name}')`);
            out.push(`class ${getTypeName(type)} extends ${baseType} {}`);
            out.push('');
        }
        else if (type.fields) {
            const baseClass = type.base ? snakeToPascal(type.base.name) : 'Struct';
            out.push(`@Struct.type('${type.name}')`);
            out.push(`export class ${getTypeName(type)} extends ${baseClass} {`);
            for (const field of type.fields) {
                let fieldType = getTypeName(field.type);
                let fieldDef = fieldType;
                if (field.type.name === 'string' || field.type.name === 'bool') {
                    fieldType = field.type.name === 'string' ? 'string' : 'boolean';
                    fieldDef = `'${field.type.typeName}'`;
                }
                else if (field.type.isArray || field.type.isExtension || field.type.isOptional) {
                    const fieldOpts = [];
                    if (field.type.isOptional) {
                        fieldOpts.push('optional: true');
                    }
                    if (field.type.isArray) {
                        fieldOpts.push('array: true');
                    }
                    if (field.type.isExtension) {
                        fieldOpts.push('extension: true');
                    }
                    fieldDef += `, {${fieldOpts.join(',')}}`;
                }
                out.push(`    @Struct.field(${fieldDef}) ${field.name}${field.type.isOptional ? '?' : '!'}: ${fieldType}${field.type.isArray ? '[]' : ''}`);
            }
            out.push('}');
            out.push('');
        }
        else if (type.variant) {
            const variantTypes = type.variant.map((t) => {
                if (t.name === 'bool' || t.name === 'string') {
                    return t.typeName;
                }
                const name = getTypeName(t);
                if (t.isArray || t.isExtension || t.isOptional) {
                    let def = `{type: ${name}`;
                    if (t.isArray) {
                        def += ', array: true';
                    }
                    if (t.isOptional) {
                        def += ', optional: true';
                    }
                    if (t.isExtension) {
                        def += ', extension: true';
                    }
                    def += '}';
                    return def;
                }
                return name;
            });
            out.push(`@Variant.type('${type.name}', [${variantTypes.join(', ')}])`);
            out.push(`class ${getTypeName(type)} extends Variant {}`);
            out.push('');
        }
    }
    const sortedImports = Array.from(imports).sort((a, b) => a.localeCompare(b));
    if (sortedImports.length > 0) {
        let importDef = sortedImports.join(', ');
        if (importDef.length > 70) {
            importDef = '\n    ' + importDef.replace(/, /g, ',\n    ') + ',\n';
        }
        out.unshift(`import {${importDef}} from '@greymass/eosio'`);
        out.unshift('');
    }
    while (out[out.length - 1] === '') {
        out.splice(out.length - 1, 1);
    }
    out.unshift('// generated by @greymass/abi2core');
    return { out };
}
/** Return PascalCase version of snake_case string. */
function snakeToPascal(name) {
    return name
        .split('_')
        .map((v) => (v[0] ? v[0].toUpperCase() : '_') + v.slice(1))
        .join('');
}
function getBuiltin(type) {
    switch (type.name) {
        case 'asset':
            return { name: 'Asset', import: 'Asset' };
        case 'symbol':
            return { name: 'Asset.Symbol', import: 'Asset' };
        case 'symbol_code':
            return { name: 'Asset.SymbolCode', import: 'Asset' };
        case 'block_timestamp':
            return { name: 'BlockTimestamp', import: 'BlockTimestamp' };
        case 'bytes':
            return { name: 'Bytes', import: 'Bytes' };
        case 'checksum160':
            return { name: 'Checksum160', import: 'Checksum160' };
        case 'checksum256':
            return { name: 'Checksum256', import: 'Checksum256' };
        case 'checksum512':
            return { name: 'Checksum512', import: 'Checksum512' };
        case 'extended_asset':
            return { name: 'ExtendedAsset', import: 'ExtendedAsset' };
        case 'float32':
            return { name: 'Float32', import: 'Float32' };
        case 'float64':
            return { name: 'Float64', import: 'Float64' };
        case 'float128':
            return { name: 'Float128', import: 'Float128' };
        case 'uint8':
            return { name: 'UInt8', import: 'UInt8' };
        case 'uint16':
            return { name: 'UInt16', import: 'UInt16' };
        case 'uint32':
            return { name: 'UInt32', import: 'UInt32' };
        case 'uint64':
            return { name: 'UInt64', import: 'UInt64' };
        case 'uint128':
            return { name: 'UInt128', import: 'UInt128' };
        case 'int8':
            return { name: 'Int8', import: 'Int8' };
        case 'int16':
            return { name: 'Int16', import: 'Int16' };
        case 'int32':
            return { name: 'Int32', import: 'Int32' };
        case 'int64':
            return { name: 'Int64', import: 'Int64' };
        case 'int128':
            return { name: 'Int128', import: 'Int128' };
        case 'varint32':
            return { name: 'VarInt', import: 'VarInt' };
        case 'varuint32':
            return { name: 'VarUInt', import: 'VarUInt' };
        case 'name':
            return { name: 'Name', import: 'Name' };
        case 'public_key':
            return { name: 'PublicKey', import: 'PublicKey' };
        case 'signature':
            return { name: 'Signature', import: 'Signature' };
        case 'time_point':
            return { name: 'TimePoint', import: 'TimePoint' };
        case 'time_point_sec':
            return { name: 'TimePointSec', import: 'TimePointSec' };
        case 'block_timestamp_type':
            return { name: 'BlockTimestamp', import: 'BlockTimestamp' };
        default:
            return null;
    }
}
/** Makes sure the type names declared by the ABI are valid TypeScript. */
function sanitizeTypeName(name) {
    return name.replace(/[^a-zA-Z0-9_]/g, '_');
}

function main(args) {
    return tslib.__awaiter(this, void 0, void 0, function* () {
        const input = args.input ? fs.createReadStream(args.input) : process.stdin;
        const output = args.output
            ? fs.createWriteStream(args.output)
            : process.stdout;
        let data = yield readJSONStream(input);
        if (data.abi && data.account_name) {
            data = data.abi;
        }
        const result = transform(data);
        for (const line of result.out) {
            output.write(line + '\n');
        }
        output.end();
    });
}
function readJSONStream(stream) {
    return new Promise((resolve, reject) => {
        const chunks = [];
        stream.on('data', (chunk) => {
            chunks.push(chunk);
        });
        stream.on('error', reject);
        stream.on('end', () => {
            try {
                resolve(JSON.parse(Buffer.concat(chunks).toString('utf8')));
            }
            catch (error) {
                error.message = `Unable to parse JSON: ${error.message}`;
                reject(error);
            }
        });
    });
}
if (module == require.main) {
    function log(...args) {
        process.stderr.write(args.join(' ') + '\n');
    }
    const parser = new argparse.ArgumentParser({ add_help: true });
    parser.add_argument('-o', '--output', {
        nargs: '?',
        help: 'Output file to write to instead of stdout.',
    });
    parser.add_argument('-i', '--input', {
        nargs: '?',
        help: 'Read ABI JSON from file instead of stdin.',
    });
    main(parser.parse_args()).catch((error) => {
        log('ERROR', error.message);
    });
}

exports.main = main;
exports.transform = transform;
//# sourceMappingURL=abi2core.js.map
