/**
 * EOSIO Core v0.5.5
 * https://github.com/greymass/eosio-core
 *
 * @license
 * Copyright (c) 2020 FFF00 Agents AB & Greymass Inc. All Rights Reserved.
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
import rand from 'brorand';
import { sha256, sha512, ripemd160 } from 'hash.js';
import BN from 'bn.js';
import { ec } from 'elliptic';
import { __decorate } from 'tslib';

function arrayEquals(a, b) {
    const len = a.length;
    if (len !== b.length) {
        return false;
    }
    for (let i = 0; i < len; i++) {
        if (a[i] !== b[i]) {
            return false;
        }
    }
    return true;
}
function arrayEquatableEquals(a, b) {
    const len = a.length;
    if (len !== b.length) {
        return false;
    }
    for (let i = 0; i < len; i++) {
        if (!a[i].equals(b[i])) {
            return false;
        }
    }
    return true;
}
const hexLookup = {};
function buildHexLookup() {
    hexLookup.enc = new Array(0xff);
    hexLookup.dec = {};
    for (let i = 0; i <= 0xff; ++i) {
        const b = i.toString(16).padStart(2, '0');
        hexLookup.enc[i] = b;
        hexLookup.dec[b] = i;
    }
}
function arrayToHex(array) {
    if (!hexLookup.enc) {
        buildHexLookup();
    }
    const len = array.length;
    const rv = new Array(len);
    for (let i = 0; i < len; ++i) {
        rv[i] = hexLookup.enc[array[i]];
    }
    return rv.join('');
}
function hexToArray(hex) {
    if (!hexLookup.dec) {
        buildHexLookup();
    }
    if (typeof hex !== 'string') {
        throw new Error('Expected string containing hex digits');
    }
    if (hex.length % 2) {
        throw new Error('Odd number of hex digits');
    }
    hex = hex.toLowerCase();
    const len = hex.length / 2;
    const result = new Uint8Array(len);
    for (let i = 0; i < len; i++) {
        const b = hexLookup.dec[hex[i * 2] + hex[i * 2 + 1]];
        if (b === undefined) {
            throw new Error('Expected hex string');
        }
        result[i] = b;
    }
    return result;
}
/** Generate N random bytes, throws if a secure random source isn't available. */
function secureRandom(length) {
    return rand(length);
}
/** Used in isInstanceOf checks so we don't spam with warnings. */
let didWarn = false;
/** Check if object in instance of class. */
function isInstanceOf(object, someClass) {
    if (object instanceof someClass) {
        return true;
    }
    if (object == null || typeof object !== 'object') {
        return false;
    }
    // not an actual instance but since bundlers can fail to dedupe stuff or
    // multiple versions can be included we check for compatibility if possible
    const className = someClass['__className'] || someClass['abiName'];
    if (!className) {
        return false;
    }
    let instanceClass = object.constructor;
    let isAlienInstance = false;
    while (instanceClass && !isAlienInstance) {
        const instanceClassName = instanceClass['__className'] || instanceClass['abiName'];
        if (!instanceClassName) {
            break;
        }
        isAlienInstance = className == instanceClassName;
        instanceClass = Object.getPrototypeOf(instanceClass);
    }
    if (isAlienInstance && !didWarn) {
        // eslint-disable-next-line no-console
        console.warn(`Detected alien instance of ${className}, this usually means more than one version of @greymass/eosio has been included in your bundle.`);
        didWarn = true;
    }
    return isAlienInstance;
}

class Bytes {
    constructor(array = new Uint8Array()) {
        this.array = array;
    }
    /**
     * Create a new Bytes instance.
     * @note Make sure to take a [[copy]] before mutating the bytes as the underlying source is not copied here.
     */
    static from(value, encoding) {
        if (isInstanceOf(value, this)) {
            return value;
        }
        if (typeof value === 'string') {
            return this.fromString(value, encoding);
        }
        if (ArrayBuffer.isView(value)) {
            return new this(new Uint8Array(value.buffer, value.byteOffset, value.byteLength));
        }
        if (isInstanceOf(value['array'], Uint8Array)) {
            return new this(value['array']);
        }
        return new this(new Uint8Array(value));
    }
    static fromString(value, encoding = 'hex') {
        if (encoding === 'hex') {
            const array = hexToArray(value);
            return new this(array);
        }
        else if (encoding == 'utf8') {
            const encoder = new TextEncoder();
            return new this(encoder.encode(value));
        }
        else {
            throw new Error(`Unknown encoding: ${encoding}`);
        }
    }
    static fromABI(decoder) {
        const len = decoder.readVaruint32();
        return new this(decoder.readArray(len));
    }
    static equal(a, b) {
        return this.from(a).equals(this.from(b));
    }
    static random(length) {
        return new this(secureRandom(length));
    }
    /** Return true if given value is a valid `BytesType`. */
    static isBytes(value) {
        if (isInstanceOf(value, Bytes) || isInstanceOf(value, Uint8Array)) {
            return true;
        }
        if (Array.isArray(value) && value.every((v) => typeof v === 'number')) {
            return true;
        }
        if (typeof value === 'string' && (/[\da-f]/i.test(value) || value === '')) {
            return true;
        }
        return false;
    }
    get hexString() {
        return arrayToHex(this.array);
    }
    get utf8String() {
        return new TextDecoder().decode(this.array);
    }
    /** Mutating. Append bytes to this instance. */
    append(other) {
        other = Bytes.from(other);
        const newSize = this.array.byteLength + other.array.byteLength;
        const buffer = new ArrayBuffer(newSize);
        const array = new Uint8Array(buffer);
        array.set(this.array);
        array.set(other.array, this.array.byteLength);
        this.array = array;
    }
    /** Non-mutating, returns a copy of this instance with appended bytes. */
    appending(other) {
        const rv = new Bytes(this.array);
        rv.append(other);
        return rv;
    }
    droppingFirst(n = 1) {
        return new Bytes(this.array.subarray(n));
    }
    copy() {
        const buffer = new ArrayBuffer(this.array.byteLength);
        const array = new Uint8Array(buffer);
        array.set(this.array);
        return new Bytes(array);
    }
    equals(other) {
        return arrayEquals(this.array, Bytes.from(other).array);
    }
    toString(encoding = 'hex') {
        if (encoding === 'hex') {
            return this.hexString;
        }
        else if (encoding === 'utf8') {
            return this.utf8String;
        }
        else {
            throw new Error(`Unknown encoding: ${encoding}`);
        }
    }
    toABI(encoder) {
        encoder.writeVaruint32(this.array.byteLength);
        encoder.writeArray(this.array);
    }
    toJSON() {
        return this.hexString;
    }
}
Bytes.abiName = 'bytes';

class Checksum {
    constructor(array) {
        const byteSize = this.constructor.byteSize;
        if (array.byteLength !== byteSize) {
            throw new Error(`Checksum size mismatch, expected ${byteSize} bytes got ${array.byteLength}`);
        }
        this.array = array;
    }
    static from(value) {
        if (isInstanceOf(value, this)) {
            return value;
        }
        if (isInstanceOf(value, Checksum)) {
            return new this(value.array);
        }
        return new this(Bytes.from(value).array);
    }
    static fromABI(decoder) {
        return new this(decoder.readArray(this.byteSize));
    }
    equals(other) {
        const self = this.constructor;
        try {
            return arrayEquals(this.array, self.from(other).array);
        }
        catch {
            return false;
        }
    }
    get hexString() {
        return arrayToHex(this.array);
    }
    toABI(encoder) {
        encoder.writeArray(this.array);
    }
    toString() {
        return this.hexString;
    }
    toJSON() {
        return this.toString();
    }
}
Checksum.abiName = '__checksum';
class Checksum256 extends Checksum {
    static from(value) {
        return super.from(value);
    }
    static hash(data) {
        const digest = new Uint8Array(sha256().update(Bytes.from(data).array).digest());
        return new Checksum256(digest);
    }
}
Checksum256.abiName = 'checksum256';
Checksum256.byteSize = 32;
class Checksum512 extends Checksum {
    static from(value) {
        return super.from(value);
    }
    static hash(data) {
        const digest = new Uint8Array(sha512().update(Bytes.from(data).array).digest());
        return new Checksum512(digest);
    }
}
Checksum512.abiName = 'checksum512';
Checksum512.byteSize = 64;
class Checksum160 extends Checksum {
    static from(value) {
        return super.from(value);
    }
    static hash(data) {
        const digest = new Uint8Array(ripemd160().update(Bytes.from(data).array).digest());
        return new Checksum160(digest);
    }
}
Checksum160.abiName = 'checksum160';
Checksum160.byteSize = 20;

/** Supported EOSIO curve types. */
var KeyType;
(function (KeyType) {
    KeyType["K1"] = "K1";
    KeyType["R1"] = "R1";
    KeyType["WA"] = "WA";
})(KeyType || (KeyType = {}));
(function (KeyType) {
    function indexFor(value) {
        switch (value) {
            case KeyType.K1:
                return 0;
            case KeyType.R1:
                return 1;
            case KeyType.WA:
                return 2;
            default:
                throw new Error(`Unknown curve type: ${value}`);
        }
    }
    KeyType.indexFor = indexFor;
    function from(value) {
        let index;
        if (typeof value !== 'number') {
            index = KeyType.indexFor(value);
        }
        else {
            index = value;
        }
        switch (index) {
            case 0:
                return KeyType.K1;
            case 1:
                return KeyType.R1;
            case 2:
                return KeyType.WA;
            default:
                throw new Error('Unknown curve type');
        }
    }
    KeyType.from = from;
})(KeyType || (KeyType = {}));

/**
 * Binary integer with the underlying value represented by a BN.js instance.
 * Follows C++11 standard for arithmetic operators and conversions.
 * @note This type is optimized for correctness not speed, if you plan to manipulate
 *       integers in a tight loop you're advised to use the underlying BN.js value or
 *       convert to a JavaScript number first.
 */
class Int {
    /**
     * Create a new instance, don't use this directly. Use the `.from` factory method instead.
     * @throws If the value over- or under-flows the integer type.
     */
    constructor(value) {
        const self = this.constructor;
        if (self.isSigned === undefined || self.byteWidth === undefined) {
            throw new Error('Cannot instantiate abstract class Int');
        }
        if (value.gt(self.max)) {
            throw new Error(`Number ${value} overflows ${self.abiName}`);
        }
        if (value.lt(self.min)) {
            throw new Error(`Number ${value} underflows ${self.abiName}`);
        }
        this.value = value;
    }
    /** Largest value that can be represented by this integer type. */
    static get max() {
        return new BN(2).pow(new BN(this.byteWidth * 8 - (this.isSigned ? 1 : 0))).isubn(1);
    }
    /** Smallest value that can be represented by this integer type. */
    static get min() {
        return this.isSigned ? this.max.ineg().isubn(1) : new BN(0);
    }
    /** Add `lhs` to `rhs` and return the resulting value. */
    static add(lhs, rhs, overflow = 'truncate') {
        return Int.operator(lhs, rhs, overflow, (a, b) => a.add(b));
    }
    /** Add `lhs` to `rhs` and return the resulting value. */
    static sub(lhs, rhs, overflow) {
        return Int.operator(lhs, rhs, overflow, (a, b) => a.sub(b));
    }
    /** Multiply `lhs` by `rhs` and return the resulting value. */
    static mul(lhs, rhs, overflow) {
        return Int.operator(lhs, rhs, overflow, (a, b) => a.mul(b));
    }
    /**
     * Divide `lhs` by `rhs` and return the quotient, dropping the remainder.
     * @throws When dividing by zero.
     */
    static div(lhs, rhs, overflow) {
        return Int.operator(lhs, rhs, overflow, (a, b) => {
            if (b.isZero()) {
                throw new Error('Division by zero');
            }
            return a.div(b);
        });
    }
    /**
     * Divide `lhs` by `rhs` and return the quotient + remainder rounded to the closest integer.
     * @throws When dividing by zero.
     */
    static divRound(lhs, rhs, overflow) {
        return Int.operator(lhs, rhs, overflow, (a, b) => {
            if (b.isZero()) {
                throw new Error('Division by zero');
            }
            return a.divRound(b);
        });
    }
    /**
     * Divide `lhs` by `rhs` and return the quotient + remainder rounded up to the closest integer.
     * @throws When dividing by zero.
     */
    static divCeil(lhs, rhs, overflow) {
        return Int.operator(lhs, rhs, overflow, (a, b) => {
            if (b.isZero()) {
                throw new Error('Division by zero');
            }
            const dm = a.divmod(b);
            if (dm.mod.isZero())
                return dm.div;
            return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
        });
    }
    /**
     * Can be used to implement custom operator.
     * @internal
     */
    static operator(lhs, rhs, overflow = 'truncate', fn) {
        const { a, b } = convert(lhs, rhs);
        const type = a.constructor;
        const result = fn(a.value, b.value);
        return type.from(result, overflow);
    }
    static from(value, overflow) {
        if (isInstanceOf(value, this)) {
            return value;
        }
        let fromType = this;
        let bn;
        if (isInstanceOf(value, Int)) {
            fromType = value.constructor;
            bn = value.value.clone();
        }
        else if (value instanceof Uint8Array) {
            bn = new BN(value, undefined, 'le');
            if (fromType.isSigned) {
                bn = bn.fromTwos(fromType.byteWidth * 8);
            }
        }
        else {
            if ((typeof value === 'string' && !/[0-9]+/.test(value)) ||
                (typeof value === 'number' && !Number.isFinite(value))) {
                throw new Error('Invalid number');
            }
            bn = BN.isBN(value) ? value.clone() : new BN(value, 10);
            if (bn.isNeg() && !fromType.isSigned) {
                fromType = { byteWidth: fromType.byteWidth, isSigned: true };
            }
        }
        switch (overflow) {
            case 'clamp':
                bn = clamp(bn, this.min, this.max);
                break;
            case 'truncate':
                bn = truncate(bn, fromType, this);
                break;
        }
        return new this(bn);
    }
    static fromABI(decoder) {
        return this.from(decoder.readArray(this.byteWidth));
    }
    static random() {
        return this.from(secureRandom(this.byteWidth));
    }
    cast(type, overflow = 'truncate') {
        if (this.constructor === type) {
            return this;
        }
        return type.from(this, overflow);
    }
    /** Number as bytes in little endian (matches memory layout in C++ contract). */
    get byteArray() {
        const self = this.constructor;
        const value = self.isSigned ? this.value.toTwos(self.byteWidth * 8) : this.value;
        return value.toArrayLike(Uint8Array, 'le', self.byteWidth);
    }
    /**
     * Compare two integers, if strict is set to true the test will only consider integers
     * of the exact same type. I.e. Int64.from(1).equals(UInt64.from(1)) will return false.
     */
    equals(other, strict = false) {
        const self = this.constructor;
        if (strict === true && isInstanceOf(other, Int)) {
            const otherType = other.constructor;
            if (self.byteWidth !== otherType.byteWidth || self.isSigned !== otherType.isSigned) {
                return false;
            }
        }
        try {
            return this.value.eq(self.from(other).value);
        }
        catch {
            return false;
        }
    }
    /** Mutating add. */
    add(num) {
        this.value = this.operator(num, Int.add).value;
    }
    /** Non-mutating add. */
    adding(num) {
        return this.operator(num, Int.add);
    }
    /** Mutating subtract. */
    subtract(num) {
        this.value = this.operator(num, Int.sub).value;
    }
    /** Non-mutating subtract. */
    subtracting(num) {
        return this.operator(num, Int.sub);
    }
    /** Mutating multiply. */
    multiply(by) {
        this.value = this.operator(by, Int.mul).value;
    }
    /** Non-mutating multiply. */
    multiplying(by) {
        return this.operator(by, Int.mul);
    }
    /**
     * Mutating divide.
     * @param behavior How to handle the remainder, default is to floor (round down).
     * @throws When dividing by zero.
     */
    divide(by, behavior) {
        this.value = this.dividing(by, behavior).value;
    }
    /**
     * Non-mutating divide.
     * @param behavior How to handle the remainder, default is to floor (round down).
     * @throws When dividing by zero.
     */
    dividing(by, behavior) {
        let op = Int.div;
        switch (behavior) {
            case 'ceil':
                op = Int.divCeil;
                break;
            case 'round':
                op = Int.divRound;
                break;
        }
        return this.operator(by, op);
    }
    /**
     * Run operator with C++11 implicit conversion.
     * @internal
     */
    operator(other, fn) {
        let rhs;
        if (isInstanceOf(other, Int)) {
            rhs = other;
        }
        else {
            rhs = Int64.from(other, 'truncate');
        }
        return fn(this, rhs).cast(this.constructor);
    }
    /**
     * Convert to a JavaScript number.
     * @throws If the number cannot be represented by 53-bits.
     **/
    toNumber() {
        return this.value.toNumber();
    }
    toString() {
        return this.value.toString();
    }
    [Symbol.toPrimitive](type) {
        if (type === 'number') {
            return this.toNumber();
        }
        else {
            return this.toString();
        }
    }
    toABI(encoder) {
        encoder.writeArray(this.byteArray);
    }
    toJSON() {
        // match FCs behavior and return strings for anything above 32-bit
        if (this.value.bitLength() > 32) {
            return this.value.toString();
        }
        else {
            return this.value.toNumber();
        }
    }
}
Int.abiName = '__int';
class Int8 extends Int {
}
Int8.abiName = 'int8';
Int8.byteWidth = 1;
Int8.isSigned = true;
class Int16 extends Int {
}
Int16.abiName = 'int16';
Int16.byteWidth = 2;
Int16.isSigned = true;
class Int32 extends Int {
}
Int32.abiName = 'int32';
Int32.byteWidth = 4;
Int32.isSigned = true;
class Int64 extends Int {
}
Int64.abiName = 'int64';
Int64.byteWidth = 8;
Int64.isSigned = true;
class Int128 extends Int {
}
Int128.abiName = 'int128';
Int128.byteWidth = 16;
Int128.isSigned = true;
class UInt8 extends Int {
}
UInt8.abiName = 'uint8';
UInt8.byteWidth = 1;
UInt8.isSigned = false;
class UInt16 extends Int {
}
UInt16.abiName = 'uint16';
UInt16.byteWidth = 2;
UInt16.isSigned = false;
class UInt32 extends Int {
}
UInt32.abiName = 'uint32';
UInt32.byteWidth = 4;
UInt32.isSigned = false;
class UInt64 extends Int {
}
UInt64.abiName = 'uint64';
UInt64.byteWidth = 8;
UInt64.isSigned = false;
class UInt128 extends Int {
}
UInt128.abiName = 'uint128';
UInt128.byteWidth = 16;
UInt128.isSigned = false;
class VarInt extends Int {
    static fromABI(decoder) {
        return new this(new BN(decoder.readVarint32()));
    }
    toABI(encoder) {
        encoder.writeVarint32(Number(this));
    }
}
VarInt.abiName = 'varint32';
VarInt.byteWidth = 32;
VarInt.isSigned = true;
class VarUInt extends Int {
    static fromABI(decoder) {
        return new this(new BN(decoder.readVaruint32()));
    }
    toABI(encoder) {
        encoder.writeVaruint32(Number(this));
    }
}
VarUInt.abiName = 'varuint32';
VarUInt.byteWidth = 32;
VarUInt.isSigned = false;
/** Clamp number between min and max. */
function clamp(num, min, max) {
    return BN.min(BN.max(num, min), max);
}
/**
 * Create new BN with the same bit pattern as the passed value,
 * extending or truncating the value’s representation as necessary.
 */
function truncate(value, from, to) {
    const fill = value.isNeg() ? 255 : 0;
    const fromValue = from.isSigned ? value.toTwos(from.byteWidth * 8) : value;
    const fromBytes = fromValue.toArrayLike(Uint8Array, 'le');
    const toBytes = new Uint8Array(to.byteWidth);
    toBytes.fill(fill);
    toBytes.set(fromBytes.slice(0, to.byteWidth));
    const toValue = new BN(toBytes, undefined, 'le');
    return to.isSigned ? toValue.fromTwos(to.byteWidth * 8) : toValue;
}
/** C++11 implicit integer conversions. */
function convert(a, b) {
    // The integral promotions (4.5) shall be performed on both operands.
    a = promote(a);
    b = promote(b);
    const aType = a.constructor;
    const bType = b.constructor;
    // If both operands have the same type, no further conversion is needed
    if (aType !== bType) {
        // Otherwise, if both operands have signed integer types or both have unsigned integer types,
        // the operand with the type of lesser integer conversion rank shall be converted to the type
        // of the operand with greater rank.
        if (aType.isSigned === bType.isSigned) {
            if (aType.byteWidth > bType.byteWidth) {
                b = b.cast(aType);
            }
            else if (bType.byteWidth > aType.byteWidth) {
                a = a.cast(bType);
            }
        }
        else {
            // Otherwise, if the operand that has unsigned integer type has rank greater than or equal
            // to the rank of the type of the other operand, the operand with signed integer type
            // shall be converted to the type of the operand with unsigned integer type.
            if (aType.isSigned === false && aType.byteWidth >= bType.byteWidth) {
                b = b.cast(aType);
            }
            else if (bType.isSigned === false && bType.byteWidth >= aType.byteWidth) {
                a = a.cast(bType);
            }
            else {
                // Otherwise, if the type of the operand with signed integer type can represent all of the
                // values of the type of the operand with unsigned integer type, the operand with unsigned
                // integer type shall be converted to the type of the operand with signed integer type.
                if (aType.isSigned === true &&
                    aType.max.gte(bType.max) &&
                    aType.min.lte(bType.min)) {
                    b = b.cast(aType);
                }
                else if (bType.isSigned === true &&
                    bType.max.gte(aType.max) &&
                    bType.min.lte(aType.min)) {
                    a = a.cast(bType);
                }
                else ;
            }
        }
    }
    return { a, b };
}
/** C++11 integral promotion. */
function promote(n) {
    // An rvalue of type char, signed char, unsigned char, short int, or
    // unsigned short int can be converted to an rvalue of type int if int
    // can represent all the values of the source type; otherwise, the source
    // rvalue can be converted to an rvalue of type unsigned int.
    let rv = n;
    const type = n.constructor;
    if (type.byteWidth < 4) {
        rv = n.cast(Int32);
    }
    return rv;
}

/** Return a ABI definition for given ABISerializableType. */
function synthesizeABI(type) {
    const structs = [];
    const variants = [];
    const aliases = [];
    const seen = new Set();
    const resolveAbiType = (t) => {
        let typeName;
        if (typeof t.type !== 'string') {
            typeName = resolve(t.type);
        }
        else {
            typeName = t.type;
        }
        if (t.array === true) {
            typeName += '[]';
        }
        if (t.extension === true) {
            typeName += '$';
        }
        if (t.optional === true) {
            typeName += '?';
        }
        return typeName;
    };
    const resolve = (t) => {
        if (!t.abiName) {
            throw new Error('Encountered non-conforming type');
        }
        else if (t.abiName === '__struct') {
            throw new Error('Misconfigured Struct subclass, did you forget @Struct.type?');
        }
        if (seen.has(t)) {
            return t.abiName;
        }
        seen.add(t);
        if (t.abiAlias) {
            aliases.push({
                new_type_name: t.abiName,
                type: resolveAbiType(t.abiAlias),
            });
        }
        else if (t.abiFields) {
            const fields = t.abiFields.map((field) => {
                return {
                    name: field.name,
                    type: resolveAbiType(field),
                };
            });
            const struct = {
                base: t.abiBase ? resolve(t.abiBase) : '',
                name: t.abiName,
                fields,
            };
            structs.push(struct);
        }
        else if (t.abiVariant) {
            const variant = {
                name: t.abiName,
                types: t.abiVariant.map(resolveAbiType),
            };
            variants.push(variant);
        }
        return t.abiName;
    };
    const root = resolve(type);
    return { abi: ABI.from({ structs, variants, types: aliases }), types: Array.from(seen), root };
}
function abiTypeString(type) {
    let typeName = typeof type.type === 'string' ? type.type : type.type.abiName;
    if (type.array === true) {
        typeName += '[]';
    }
    if (type.extension === true) {
        typeName += '$';
    }
    if (type.optional === true) {
        typeName += '?';
    }
    return typeName;
}
function isTypeDescriptor(type) {
    return (typeof type !== 'string' &&
        type.abiName === undefined &&
        type.type !== undefined);
}
function toTypeDescriptor(type) {
    if (typeof type === 'string') {
        return { type };
    }
    if (typeof type.abiName !== 'undefined') {
        return { type: type };
    }
    return type;
}

const StringType = {
    abiName: 'string',
    fromABI: (decoder) => {
        return decoder.readString();
    },
    from: (string) => string,
    toABI: (string, encoder) => {
        encoder.writeString(string);
    },
};
const BoolType = {
    abiName: 'bool',
    fromABI: (decoder) => {
        return decoder.readByte() === 1;
    },
    from: (value) => value,
    toABI: (value, encoder) => {
        encoder.writeByte(value === true ? 1 : 0);
    },
};
function getBuiltins() {
    return [
        // types represented by JavaScript builtins
        BoolType,
        StringType,
        // types represented by Classes
        Asset,
        Asset.Symbol,
        Asset.SymbolCode,
        BlockTimestamp,
        Bytes,
        Checksum160,
        Checksum256,
        Checksum512,
        ExtendedAsset,
        Float128,
        Float32,
        Float64,
        Int128,
        Int16,
        Int32,
        Int64,
        Int8,
        Name,
        PublicKey,
        Signature,
        TimePoint,
        TimePointSec,
        UInt128,
        UInt16,
        UInt32,
        UInt64,
        UInt8,
        VarInt,
        VarUInt,
    ];
}
function buildTypeLookup(additional = []) {
    const rv = {};
    const builtins = getBuiltins();
    for (const type of builtins) {
        rv[type.abiName] = type;
    }
    for (const type of additional) {
        if (!type.abiName) {
            throw new Error('Invalid type');
        }
        rv[type.abiName] = type;
    }
    return rv;
}
function getTypeName(object) {
    if (object.constructor && object.constructor.abiName !== undefined) {
        return object.constructor.abiName;
    }
    if (Array.isArray(object)) {
        const types = object.map(getTypeName);
        const type = types[0];
        if (!type || !types.every((t) => t === type)) {
            return;
        }
        return type + '[]';
    }
    switch (typeof object) {
        case 'boolean':
            return 'bool';
        case 'string':
            return 'string';
    }
}
function getType(object, name = 'jsobj') {
    var _a;
    if (object.constructor && object.constructor.abiName !== undefined) {
        return object.constructor;
    }
    if (Array.isArray(object)) {
        // check for array of all ABISerializableType with same type name
        const types = object.map((v) => {
            return getType(v, name);
        });
        const type = types[0];
        if (!type) {
            return; // some type not known
        }
        if (!types.every((t) => t && t.abiName === type.abiName)) {
            return; // not all types are the same
        }
        return type;
    }
    const objectType = typeof object;
    if (objectType === 'object' && object !== null) {
        const fields = Object.keys(object).map((key) => {
            return { name: key, type: getType(object[key], name + '_nested') };
        });
        if (fields.find((field) => !field.type)) {
            return; // encountered unknown type
        }
        return _a = class extends Struct {
            },
            _a.abiName = name,
            _a.abiFields = fields,
            _a;
    }
    switch (objectType) {
        case 'boolean':
            return BoolType;
        case 'string':
            return StringType;
    }
}

/**
 * EOSIO ABI Decoder
 */
class DecodingError extends Error {
    constructor(ctx, underlyingError) {
        const path = ctx.codingPath
            .map(({ field, type }) => {
            if (typeof field === 'number') {
                return field;
            }
            else {
                return `${field}<${type.typeName}>`;
            }
        })
            .join('.');
        super(`Decoding error at ${path}: ${underlyingError.message}`);
        this.stack = underlyingError.stack;
        this.ctx = ctx;
        this.underlyingError = underlyingError;
    }
}
DecodingError.__className = 'DecodingError';
function abiDecode(args) {
    const descriptor = toTypeDescriptor(args.type);
    const typeName = abiTypeString(descriptor);
    const customTypes = args.customTypes || [];
    let abi;
    if (args.abi) {
        abi = ABI.from(args.abi);
    }
    else {
        try {
            let type;
            if (typeof descriptor.type === 'string') {
                const lookup = buildTypeLookup(customTypes);
                const rName = new ABI.ResolvedType(descriptor.type).name; // type name w/o suffixes
                type = lookup[rName];
                if (!type) {
                    throw new Error(`Unknown type: ${descriptor.type}`);
                }
            }
            else {
                type = descriptor.type;
            }
            const synthesized = synthesizeABI(type);
            abi = synthesized.abi;
            customTypes.push(...synthesized.types);
        }
        catch (error) {
            throw Error(`Unable to synthesize ABI for: ${typeName} (${error.message}). ` +
                'To decode non-class types you need to pass the ABI definition manually.');
        }
    }
    const resolved = abi.resolveType(typeName);
    if (typeof descriptor.type !== 'string') {
        customTypes.unshift(descriptor.type);
    }
    const ctx = {
        types: buildTypeLookup(customTypes),
        codingPath: [{ field: 'root', type: resolved }],
    };
    try {
        if (args.data) {
            let decoder;
            if (isInstanceOf(args.data, ABIDecoder)) {
                decoder = args.data;
            }
            else {
                const bytes = Bytes.from(args.data);
                decoder = new ABIDecoder(bytes.array);
            }
            if (args.metadata) {
                decoder.metadata = args.metadata;
            }
            return decodeBinary(resolved, decoder, ctx);
        }
        else if (args.object !== undefined) {
            return decodeObject(args.object, resolved, ctx);
        }
        else if (args.json) {
            return decodeObject(JSON.parse(args.json), resolved, ctx);
        }
        else {
            throw new Error('Nothing to decode, you must set one of data, json, object');
        }
    }
    catch (error) {
        throw new DecodingError(ctx, error);
    }
}
/** Marker for objects when they have been resolved, i.e. their types `from` factory method will not need to resolve children. */
const Resolved = Symbol('Resolved');
function decodeBinary(type, decoder, ctx) {
    if (ctx.codingPath.length > 32) {
        throw new Error('Maximum decoding depth exceeded');
    }
    if (type.isExtension) {
        if (!decoder.canRead()) {
            return undefined;
        }
    }
    if (type.isOptional) {
        if (decoder.readByte() === 0) {
            return null;
        }
    }
    if (type.isArray) {
        const len = decoder.readVaruint32();
        const rv = [];
        for (let i = 0; i < len; i++) {
            ctx.codingPath.push({ field: i, type });
            rv.push(decodeInner());
            ctx.codingPath.pop();
        }
        return rv;
    }
    else {
        return decodeInner();
    }
    function decodeInner() {
        const abiType = ctx.types[type.name];
        if (abiType && abiType.fromABI) {
            return abiType.fromABI(decoder);
        }
        else {
            if (type.ref) {
                // follow type alias
                ctx.codingPath.push({ field: '', type: type.ref });
                const rv = decodeBinary(type.ref, decoder, ctx);
                ctx.codingPath.pop();
                return rv;
            }
            else if (type.fields) {
                const fields = type.allFields;
                if (!fields) {
                    throw new Error('Invalid struct fields');
                }
                const rv = {};
                for (const field of fields) {
                    ctx.codingPath.push({ field: field.name, type: field.type });
                    rv[field.name] = decodeBinary(field.type, decoder, ctx);
                    ctx.codingPath.pop();
                }
                if (abiType) {
                    rv[Resolved] = true;
                    return abiType.from(rv);
                }
                else {
                    return rv;
                }
            }
            else if (type.variant) {
                const vIdx = decoder.readByte();
                const vType = type.variant[vIdx];
                if (!vType) {
                    throw new Error(`Unknown variant idx: ${vIdx}`);
                }
                ctx.codingPath.push({ field: `v${vIdx}`, type: vType });
                const rv = [vType.typeName, decodeBinary(vType, decoder, ctx)];
                ctx.codingPath.pop();
                if (abiType) {
                    return abiType.from(rv);
                }
                else {
                    return rv;
                }
            }
            else if (abiType) {
                throw new Error('Invalid type');
            }
            else {
                throw new Error(type.name === 'any' ? "Unable to decode 'any' type from binary" : 'Unknown type');
            }
        }
    }
}
function decodeObject(value, type, ctx) {
    if (value === null || value === undefined) {
        if (type.isOptional || type.isExtension) {
            return null;
        }
        else {
            throw new Error(`Unexpectedly encountered ${value} for non-optional`);
        }
    }
    else if (type.isArray) {
        if (!Array.isArray(value)) {
            throw new Error('Expected array');
        }
        const rv = [];
        const len = value.length;
        for (let i = 0; i < len; i++) {
            ctx.codingPath.push({ field: i, type });
            rv.push(decodeInner(value[i]));
            ctx.codingPath.pop();
        }
        return rv;
    }
    else {
        return decodeInner(value);
    }
    function decodeInner(value) {
        const abiType = ctx.types[type.name];
        if (type.ref && !abiType) {
            // follow type alias
            return decodeObject(value, type.ref, ctx);
        }
        else if (type.fields) {
            if (typeof value !== 'object') {
                throw new Error('Expected object');
            }
            if (typeof abiType === 'function' && isInstanceOf(value, abiType)) {
                return value;
            }
            const fields = type.allFields;
            if (!fields) {
                throw new Error('Invalid struct fields');
            }
            const struct = {};
            for (const field of fields) {
                ctx.codingPath.push({ field: field.name, type: field.type });
                struct[field.name] = decodeObject(value[field.name], field.type, ctx);
                ctx.codingPath.pop();
            }
            if (abiType) {
                struct[Resolved] = true;
                return abiType.from(struct);
            }
            else {
                return struct;
            }
        }
        else if (type.variant) {
            let vName;
            if (Array.isArray(value) && value.length === 2 && typeof value[0] === 'string') {
                vName = value[0];
                value = value[1];
            }
            else if (isInstanceOf(value, Variant)) {
                vName = value.variantName;
                value = value.value;
            }
            else {
                vName = getTypeName(value);
            }
            const vIdx = type.variant.findIndex((t) => t.typeName === vName);
            if (vIdx === -1) {
                throw new Error(`Unknown variant type: ${vName}`);
            }
            const vType = type.variant[vIdx];
            ctx.codingPath.push({ field: `v${vIdx}`, type: vType });
            const rv = [vType.typeName, decodeObject(value, vType, ctx)];
            ctx.codingPath.pop();
            if (abiType) {
                rv[Resolved] = true;
                return abiType.from(rv);
            }
            else {
                return rv;
            }
        }
        else {
            if (!abiType) {
                // special case for `any` when decoding from object
                if (type.name === 'any') {
                    return value;
                }
                throw new Error('Unknown type');
            }
            return abiType.from(value);
        }
    }
}
class ABIDecoder {
    constructor(array) {
        this.array = array;
        this.pos = 0;
        this.textDecoder = new TextDecoder('utf-8', { fatal: true });
        /** User declared metadata, can be used to pass info to instances when decoding.  */
        this.metadata = {};
        this.data = new DataView(array.buffer, array.byteOffset, array.byteLength);
    }
    canRead(bytes = 1) {
        return !(this.pos + bytes > this.array.byteLength);
    }
    ensure(bytes) {
        if (!this.canRead(bytes)) {
            throw new Error('Read past end of buffer');
        }
    }
    setPosition(pos) {
        if (pos < 0 || pos > this.array.byteLength) {
            throw new Error('Invalid position');
        }
        this.pos = pos;
    }
    getPosition() {
        return this.pos;
    }
    advance(bytes) {
        this.ensure(bytes);
        this.pos += bytes;
    }
    /** Read one byte. */
    readByte() {
        this.ensure(1);
        return this.array[this.pos++];
    }
    /** Read floating point as JavaScript number, 32 or 64 bits. */
    readFloat(byteWidth) {
        this.ensure(byteWidth);
        let rv;
        switch (byteWidth) {
            case 4:
                rv = this.data.getFloat32(this.pos, true);
                break;
            case 8:
                rv = this.data.getFloat64(this.pos, true);
                break;
            default:
                throw new Error('Invalid float size');
        }
        this.pos += byteWidth;
        return rv;
    }
    readVaruint32() {
        let v = 0;
        let bit = 0;
        for (;;) {
            const b = this.readByte();
            v |= (b & 0x7f) << bit;
            bit += 7;
            if (!(b & 0x80)) {
                break;
            }
        }
        return v >>> 0;
    }
    readVarint32() {
        const v = this.readVaruint32();
        if (v & 1) {
            return (~v >> 1) | 2147483648;
        }
        else {
            return v >>> 1;
        }
    }
    readArray(length) {
        this.ensure(length);
        const rv = this.array.subarray(this.pos, this.pos + length);
        this.pos += length;
        return rv;
    }
    readString() {
        const length = this.readVaruint32();
        return this.textDecoder.decode(this.readArray(length));
    }
}
ABIDecoder.__className = 'ABIDecoder';

/**
 * EOSIO ABI Encoder
 */
class EncodingError extends Error {
    constructor(ctx, underlyingError) {
        const path = ctx.codingPath
            .map(({ field, type }) => {
            if (typeof field === 'number') {
                return field;
            }
            else {
                return `${field}<${type.typeName}>`;
            }
        })
            .join('.');
        super(`Encoding error at ${path}: ${underlyingError.message}`);
        this.stack = underlyingError.stack;
        this.ctx = ctx;
        this.underlyingError = underlyingError;
    }
}
EncodingError.__className = 'EncodingError';
function abiEncode(args) {
    let type;
    let typeName;
    if (typeof args.type === 'string') {
        typeName = args.type;
    }
    else if (args.type && isTypeDescriptor(args.type)) {
        if (typeof args.type.type !== 'string') {
            type = args.type.type;
        }
        typeName = abiTypeString(args.type);
    }
    else if (args.type && args.type.abiName !== undefined) {
        type = args.type;
        typeName = args.type.abiName;
    }
    else {
        type = getType(args.object);
        if (type) {
            typeName = type.abiName;
            if (Array.isArray(args.object)) {
                typeName += '[]';
            }
        }
    }
    const customTypes = args.customTypes ? args.customTypes.slice() : [];
    if (type) {
        customTypes.unshift(type);
    }
    else if (typeName) {
        const rootName = new ABI.ResolvedType(typeName).name;
        type = customTypes.find((t) => t.abiName === rootName);
    }
    let rootType;
    if (args.abi && typeName) {
        rootType = ABI.from(args.abi).resolveType(typeName);
    }
    else if (type) {
        const synthesized = synthesizeABI(type);
        rootType = synthesized.abi.resolveType(typeName || type.abiName);
        customTypes.push(...synthesized.types);
    }
    else if (typeName) {
        rootType = new ABI.ResolvedType(typeName);
    }
    else {
        throw new Error('Unable to determine the type of the object to be encoded. ' +
            'To encode custom ABI types you must pass the type argument.');
    }
    const types = buildTypeLookup(customTypes);
    const encoder = args.encoder || new ABIEncoder();
    if (args.metadata) {
        encoder.metadata = args.metadata;
    }
    const ctx = {
        types,
        encoder,
        codingPath: [{ field: 'root', type: rootType }],
    };
    try {
        encodeAny(args.object, rootType, ctx);
    }
    catch (error) {
        throw new EncodingError(ctx, error);
    }
    return Bytes.from(encoder.getData());
}
function encodeAny(value, type, ctx) {
    const valueExists = value !== undefined && value !== null;
    if (type.isOptional) {
        ctx.encoder.writeByte(valueExists ? 1 : 0);
        if (!valueExists) {
            return;
        }
    }
    if (type.isArray) {
        if (!Array.isArray(value)) {
            throw new Error(`Expected array for: ${type.typeName}`);
        }
        const len = value.length;
        ctx.encoder.writeVaruint32(len);
        for (let i = 0; i < len; i++) {
            ctx.codingPath.push({ field: i, type });
            encodeInner(value[i]);
            ctx.codingPath.pop();
        }
    }
    else {
        encodeInner(value);
    }
    function encodeInner(value) {
        const abiType = ctx.types[type.name];
        if (type.ref && !abiType) {
            // type is alias, follow it
            encodeAny(value, type.ref, ctx);
            return;
        }
        if (!valueExists) {
            if (type.isExtension) {
                return;
            }
            throw new Error(`Found ${value} for non-optional type: ${type.typeName}`);
        }
        if (abiType && abiType.toABI) {
            // type explicitly handles encoding
            abiType.toABI(value, ctx.encoder);
        }
        else if (typeof value.toABI === 'function' && value.constructor.abiName === type.name) {
            // instance handles encoding
            value.toABI(ctx.encoder);
        }
        else {
            // encode according to abi def if possible
            if (type.fields) {
                if (typeof value !== 'object') {
                    throw new Error(`Expected object for: ${type.name}`);
                }
                const fields = type.allFields;
                if (!fields) {
                    throw new Error('Invalid struct fields');
                }
                for (const field of fields) {
                    ctx.codingPath.push({ field: field.name, type: field.type });
                    encodeAny(value[field.name], field.type, ctx);
                    ctx.codingPath.pop();
                }
            }
            else if (type.variant) {
                let vName;
                if (Array.isArray(value) && value.length === 2 && typeof value[0] === 'string') {
                    vName = value[0];
                    value = value[1];
                }
                else if (isInstanceOf(value, Variant)) {
                    vName = value.variantName;
                    value = value.value;
                }
                else {
                    vName = getTypeName(value);
                }
                const vIdx = type.variant.findIndex((t) => t.typeName === vName);
                if (vIdx === -1) {
                    const types = type.variant.map((t) => `'${t.typeName}'`).join(', ');
                    throw new Error(`Unknown variant type '${vName}', expected one of ${types}`);
                }
                const vType = type.variant[vIdx];
                ctx.encoder.writeVaruint32(vIdx);
                ctx.codingPath.push({ field: `v${vIdx}`, type: vType });
                encodeAny(value, vType, ctx);
                ctx.codingPath.pop();
            }
            else {
                if (!abiType) {
                    throw new Error(type.name === 'any' ? 'Unable to encode any type to binary' : 'Unknown type');
                }
                const instance = abiType.from(value);
                if (!instance.toABI) {
                    throw new Error(`Invalid type ${type.name}, no encoding methods implemented`);
                }
                instance.toABI(ctx.encoder);
            }
        }
    }
}
class ABIEncoder {
    constructor(pageSize = 1024) {
        this.pageSize = pageSize;
        this.pos = 0;
        this.textEncoder = new TextEncoder();
        /** User declared metadata, can be used to pass info to instances when encoding.  */
        this.metadata = {};
        const buffer = new ArrayBuffer(pageSize);
        this.data = new DataView(buffer);
        this.array = new Uint8Array(buffer);
    }
    ensure(bytes) {
        if (this.data.byteLength >= this.pos + bytes) {
            return;
        }
        const pages = Math.ceil(bytes / this.pageSize);
        const newSize = this.data.byteLength + this.pageSize * pages;
        const buffer = new ArrayBuffer(newSize);
        const data = new DataView(buffer);
        const array = new Uint8Array(buffer);
        array.set(this.array);
        this.data = data;
        this.array = array;
    }
    /** Write a single byte. */
    writeByte(byte) {
        this.ensure(1);
        this.array[this.pos++] = byte;
    }
    /** Write an array of bytes. */
    writeArray(bytes) {
        const size = bytes.length;
        this.ensure(size);
        this.array.set(bytes, this.pos);
        this.pos += size;
    }
    writeFloat(value, byteWidth) {
        this.ensure(byteWidth);
        switch (byteWidth) {
            case 4:
                this.data.setFloat32(this.pos, value, true);
                break;
            case 8:
                this.data.setFloat64(this.pos, value, true);
                break;
            default:
                throw new Error('Invalid float size');
        }
        this.pos += byteWidth;
    }
    writeVaruint32(v) {
        this.ensure(4);
        for (;;) {
            if (v >>> 7) {
                this.array[this.pos++] = 0x80 | (v & 0x7f);
                v = v >>> 7;
            }
            else {
                this.array[this.pos++] = v;
                break;
            }
        }
    }
    writeVarint32(v) {
        this.writeVaruint32((v << 1) ^ (v >> 31));
    }
    writeString(v) {
        const data = this.textEncoder.encode(v);
        this.writeVaruint32(data.byteLength);
        this.writeArray(data);
    }
    getData() {
        return new Uint8Array(this.array.buffer, this.array.byteOffset, this.pos);
    }
    getBytes() {
        return new Bytes(this.getData());
    }
}
ABIEncoder.__className = 'ABIEncoder';

class Struct {
    /** @internal */
    constructor(object) {
        const self = this.constructor;
        for (const field of self.structFields) {
            this[field.name] = object[field.name];
        }
    }
    static from(value) {
        if (value[Resolved] === true) {
            // objects already resolved
            return new this(value);
        }
        if (isInstanceOf(value, this)) {
            return value;
        }
        const object = {};
        for (const field of this.structFields) {
            const v = value[field.name] === undefined ? field.default : value[field.name];
            object[field.name] = v;
        }
        return abiDecode({ object, type: this });
    }
    static get structFields() {
        const rv = [];
        const walk = (t) => {
            if (t.abiBase) {
                walk(t.abiBase);
            }
            for (const field of t.abiFields || []) {
                rv.push(field);
            }
        };
        walk(this);
        return rv;
    }
    /**
     * Return true if this struct equals the other.
     *
     * Note: This compares the ABI encoded bytes of both structs, subclasses
     *       should implement their own fast equality check when possible.
     */
    equals(other) {
        const self = this.constructor;
        if (other.constructor &&
            typeof other.constructor.abiName === 'string' &&
            other.constructor.abiName !== self.abiName) {
            return false;
        }
        return abiEncode({ object: this }).equals(abiEncode({ object: self.from(other) }));
    }
    /** @internal */
    toJSON() {
        const self = this.constructor;
        const rv = {};
        for (const field of self.structFields) {
            rv[field.name] = this[field.name];
        }
        return rv;
    }
}
Struct.abiName = '__struct';
(function (Struct) {
    const FieldsOwner = Symbol('FieldsOwner');
    function type(name) {
        return function (struct) {
            struct.abiName = name;
            return struct;
        };
    }
    Struct.type = type;
    function field(type, options) {
        if (!options)
            options = {};
        return (target, name) => {
            const ctor = target.constructor;
            if (!ctor.abiFields) {
                ctor.abiFields = [];
                ctor.abiFields[FieldsOwner] = ctor;
            }
            else if (ctor.abiFields[FieldsOwner] !== ctor) {
                // if the target class isn't the owner we set the base and start new fields
                ctor.abiBase = ctor.abiFields[FieldsOwner];
                ctor.abiFields = [];
                ctor.abiFields[FieldsOwner] = ctor;
            }
            ctor.abiFields.push({ ...options, name, type });
        };
    }
    Struct.field = field;
})(Struct || (Struct = {}));

function TypeAlias(name) {
    return function (typeAlias) {
        typeAlias.abiAlias = { type: Object.getPrototypeOf(typeAlias.prototype).constructor };
        typeAlias.abiName = name;
        return typeAlias;
    };
}

class Variant {
    /** @internal */
    constructor(variant) {
        const abiVariant = this.constructor.abiVariant;
        this.value = variant[1];
        const variantIdx = abiVariant.map(abiTypeString).findIndex((t) => t === variant[0]);
        if (0 > variantIdx || abiVariant.length <= variantIdx) {
            throw new Error(`Unknown variant ${variant[0]}`);
        }
        this.variantIdx = variantIdx;
    }
    static from(object) {
        if (object[Resolved]) {
            return new this(object);
        }
        if (isInstanceOf(object, this)) {
            return object;
        }
        return abiDecode({ object, type: this });
    }
    /**
     * Return true if this variant equals the other.
     *
     * Note: This compares the ABI encoded bytes of both variants, subclasses
     *       should implement their own fast equality check when possible.
     */
    equals(other) {
        const self = this.constructor;
        const otherVariant = self.from(other);
        if (this.variantIdx !== otherVariant.variantIdx) {
            return false;
        }
        return abiEncode({ object: this }).equals(abiEncode({ object: otherVariant }));
    }
    get variantName() {
        const variant = this.constructor.abiVariant[this.variantIdx];
        return abiTypeString(variant);
    }
    /** @internal */
    toJSON() {
        return [this.variantName, this.value];
    }
}
Variant.abiName = '__variant';
Variant.abiVariant = [];
(function (Variant) {
    function type(name, types) {
        return function (variant) {
            variant.abiName = name;
            variant.abiVariant = types.map(toTypeDescriptor);
            return variant;
        };
    }
    Variant.type = type;
})(Variant || (Variant = {}));

class Float {
    constructor(value) {
        if (!Number.isFinite(value)) {
            throw new Error('Invalid number');
        }
        this.value = value;
    }
    static from(value) {
        if (isInstanceOf(value, this)) {
            return value;
        }
        if (typeof value === 'string') {
            value = Number.parseFloat(value);
        }
        else if (isInstanceOf(value, Float)) {
            value = value.value;
        }
        return new this(value);
    }
    static fromABI(decoder) {
        return new this(decoder.readFloat(this.byteWidth));
    }
    static random() {
        const bytes = secureRandom(this.byteWidth);
        const decoder = new ABIDecoder(bytes);
        return this.fromABI(decoder);
    }
    equals(other) {
        const self = this.constructor;
        return this.value === self.from(other).value;
    }
    toABI(encoder) {
        const self = this.constructor;
        encoder.writeFloat(this.value, self.byteWidth);
    }
    toString() {
        return this.value.toString();
    }
    toJSON() {
        return this.toString();
    }
}
Float.abiName = '__float';
class Float32 extends Float {
    toString() {
        return this.value.toFixed(7);
    }
}
Float32.abiName = 'float32';
Float32.byteWidth = 4;
class Float64 extends Float {
}
Float64.abiName = 'float64';
Float64.byteWidth = 8;
class Float128 {
    constructor(data) {
        if (data.array.length !== 16) {
            throw new Error('Invalid float128');
        }
        this.data = data;
    }
    static from(value) {
        if (isInstanceOf(value, this)) {
            return value;
        }
        if (typeof value === 'string' && value.startsWith('0x')) {
            value = value.slice(2);
        }
        return new this(Bytes.from(value));
    }
    static fromABI(decoder) {
        return new this(new Bytes(decoder.readArray(this.byteWidth)));
    }
    static random() {
        const bytes = secureRandom(16);
        const decoder = new ABIDecoder(bytes);
        return this.fromABI(decoder);
    }
    equals(other) {
        const self = this.constructor;
        return this.data.equals(self.from(other).data);
    }
    toABI(encoder) {
        encoder.writeArray(this.data.array);
    }
    toString() {
        // float128 uses 0x prefixed hex strings as opposed to everywhere else in where there is no prefix ¯\_(ツ)_/¯
        return '0x' + this.data.hexString;
    }
    toJSON() {
        return this.toString();
    }
}
Float128.abiName = 'float128';
Float128.byteWidth = 16;

/** EOSIO Name */
class Name {
    constructor(value) {
        this.value = value;
    }
    /**
     * The raw representation of the name.
     * @deprecated Use value instead.
     */
    get rawValue() {
        return this.value;
    }
    /** Create a new Name instance from any of its representing types. */
    static from(value) {
        if (isInstanceOf(value, Name)) {
            return value;
        }
        else if (typeof value === 'string') {
            return new Name(stringToName(value));
        }
        else if (isInstanceOf(value, UInt64)) {
            return new Name(value);
        }
        else {
            throw new Error('Invalid name');
        }
    }
    static fromABI(decoder) {
        return new Name(UInt64.fromABI(decoder));
    }
    /** Return true if this name is equal to passed name. */
    equals(other) {
        return this.value.equals(Name.from(other).value);
    }
    /** Return string representation of this name. */
    toString() {
        return nameToString(this.value);
    }
    toABI(encoder) {
        this.value.toABI(encoder);
    }
    /** @internal */
    toJSON() {
        return this.toString();
    }
}
Name.abiName = 'name';
/** Regex pattern matching a EOSIO name, case-sensitive. */
Name.pattern = /^[a-z1-5.]{0,13}$/;
function stringToName(s) {
    function charToSymbol(c) {
        if (c >= 'a'.charCodeAt(0) && c <= 'z'.charCodeAt(0)) {
            return c - 'a'.charCodeAt(0) + 6;
        }
        if (c >= '1'.charCodeAt(0) && c <= '5'.charCodeAt(0)) {
            return c - '1'.charCodeAt(0) + 1;
        }
        return 0;
    }
    const a = new Uint8Array(8);
    let bit = 63;
    for (let i = 0; i < s.length; ++i) {
        let c = charToSymbol(s.charCodeAt(i));
        if (bit < 5) {
            c = c << 1;
        }
        for (let j = 4; j >= 0; --j) {
            if (bit >= 0) {
                a[Math.floor(bit / 8)] |= ((c >> j) & 1) << bit % 8;
                --bit;
            }
        }
    }
    return UInt64.from(a);
}
function nameToString(n) {
    const a = n.value.toArray('le', 8);
    let result = '';
    for (let bit = 63; bit >= 0;) {
        let c = 0;
        for (let i = 0; i < 5; ++i) {
            if (bit >= 0) {
                c = (c << 1) | ((a[Math.floor(bit / 8)] >> bit % 8) & 1);
                --bit;
            }
        }
        if (c >= 6) {
            result += String.fromCharCode(c + 'a'.charCodeAt(0) - 6);
        }
        else if (c >= 1) {
            result += String.fromCharCode(c + '1'.charCodeAt(0) - 1);
        }
        else {
            result += '.';
        }
    }
    while (result.endsWith('.')) {
        result = result.substr(0, result.length - 1);
    }
    return result;
}

class TimePointBase {
    static from(value) {
        if (isInstanceOf(value, this)) {
            return value;
        }
        if (isInstanceOf(value, TimePointBase)) {
            // converting between types
            return this.fromMilliseconds(value.toMilliseconds());
        }
        if (isInstanceOf(value, Date)) {
            return this.fromDate(value);
        }
        if (typeof value === 'string') {
            return this.fromString(value);
        }
        return this.fromInteger(value);
    }
    static fromString(string) {
        const value = Date.parse(string + 'Z');
        if (!Number.isFinite(value)) {
            throw new Error('Invalid date string');
        }
        return this.fromMilliseconds(value);
    }
    static fromDate(date) {
        return this.fromMilliseconds(date.getTime());
    }
    toABI(encoder) {
        const self = this;
        self.value.toABI(encoder);
    }
    equals(other) {
        const self = this.constructor;
        return this.toMilliseconds() === self.from(other).toMilliseconds();
    }
    toMilliseconds() {
        throw new Error('Not implemented');
    }
    toDate() {
        return new Date(this.toMilliseconds());
    }
    toJSON() {
        return this.toString();
    }
}
TimePointBase.abiName = '__time_point_base';
/** Timestamp with microsecond accuracy. */
class TimePoint extends TimePointBase {
    constructor(value) {
        super();
        this.value = value;
    }
    static fromMilliseconds(ms) {
        return new this(Int64.from(Math.round(ms * 1000)));
    }
    static fromInteger(value) {
        return new this(Int64.from(value));
    }
    static fromABI(decoder) {
        return new this(Int64.fromABI(decoder));
    }
    toString() {
        return this.toDate().toISOString().slice(0, -1);
    }
    toMilliseconds() {
        return Number(this.value.dividing(1000, 'round'));
    }
}
TimePoint.abiName = 'time_point';
/** Timestamp with second accuracy. */
class TimePointSec extends TimePointBase {
    constructor(value) {
        super();
        this.value = value;
    }
    static fromMilliseconds(ms) {
        return new this(UInt32.from(Math.round(ms / 1000)));
    }
    static fromInteger(value) {
        return new this(UInt32.from(value));
    }
    static fromABI(decoder) {
        return new this(UInt32.fromABI(decoder));
    }
    toString() {
        return this.toDate().toISOString().slice(0, -5);
    }
    toMilliseconds() {
        return Number(this.value.cast(UInt64).multiplying(1000));
    }
}
TimePointSec.abiName = 'time_point_sec';
class BlockTimestamp extends TimePointBase {
    constructor(value) {
        super();
        this.value = value;
    }
    static fromMilliseconds(ms) {
        return new this(UInt32.from(Math.round((ms - 946684800000) / 500)));
    }
    static fromInteger(value) {
        return new this(UInt32.from(value));
    }
    static fromABI(decoder) {
        return new this(UInt32.fromABI(decoder));
    }
    toString() {
        return this.toDate().toISOString().slice(0, -1);
    }
    toMilliseconds() {
        return Number(this.value.cast(UInt64).multiplying(500).adding(946684800000));
    }
}
BlockTimestamp.abiName = 'block_timestamp_type';

class ABI {
    constructor(args) {
        this.version = args.version || ABI.version;
        this.types = args.types || [];
        this.variants = args.variants || [];
        this.structs = args.structs || [];
        this.actions = args.actions || [];
        this.tables = args.tables || [];
        this.ricardian_clauses = args.ricardian_clauses || [];
    }
    static from(value) {
        if (isInstanceOf(value, ABI)) {
            return value;
        }
        if (typeof value === 'string') {
            return new ABI(JSON.parse(value));
        }
        return new ABI(value);
    }
    static fromABI(decoder) {
        const version = decoder.readString();
        const types = [];
        const numTypes = decoder.readVaruint32();
        for (let i = 0; i < numTypes; i++) {
            types.push({ new_type_name: decoder.readString(), type: decoder.readString() });
        }
        const structs = [];
        const numStructs = decoder.readVaruint32();
        for (let i = 0; i < numStructs; i++) {
            const name = decoder.readString();
            const base = decoder.readString();
            const numFields = decoder.readVaruint32();
            const fields = [];
            for (let j = 0; j < numFields; j++) {
                fields.push({ name: decoder.readString(), type: decoder.readString() });
            }
            structs.push({ base, name, fields });
        }
        const actions = [];
        const numActions = decoder.readVaruint32();
        for (let i = 0; i < numActions; i++) {
            const name = Name.fromABI(decoder);
            const type = decoder.readString();
            const ricardian_contract = decoder.readString();
            actions.push({ name, type, ricardian_contract });
        }
        const tables = [];
        const numTables = decoder.readVaruint32();
        for (let i = 0; i < numTables; i++) {
            const name = Name.fromABI(decoder);
            const index_type = decoder.readString();
            const key_names = [];
            const numKeyNames = decoder.readVaruint32();
            for (let j = 0; j < numKeyNames; j++) {
                key_names.push(decoder.readString());
            }
            const key_types = [];
            const numKeyTypes = decoder.readVaruint32();
            for (let j = 0; j < numKeyTypes; j++) {
                key_types.push(decoder.readString());
            }
            const type = decoder.readString();
            tables.push({ name, index_type, key_names, key_types, type });
        }
        const ricardian_clauses = [];
        const numClauses = decoder.readVaruint32();
        for (let i = 0; i < numClauses; i++) {
            const id = decoder.readString();
            const body = decoder.readString();
            ricardian_clauses.push({ id, body });
        }
        // error_messages, never used?
        const numErrors = decoder.readVaruint32();
        for (let i = 0; i < numErrors; i++) {
            decoder.advance(8); // uint64 error_code
            decoder.advance(decoder.readVaruint32()); // string error_msgr
        }
        // extensions, not used
        const numExtensions = decoder.readVaruint32();
        for (let i = 0; i < numExtensions; i++) {
            decoder.advance(2); // uint16 type
            decoder.advance(decoder.readVaruint32()); // bytes data
        }
        // variants is a binary extension for some reason even though extensions are defined on the type
        const variants = [];
        if (decoder.canRead()) {
            const numVariants = decoder.readVaruint32();
            for (let i = 0; i < numVariants; i++) {
                const name = decoder.readString();
                const types = [];
                const numTypes = decoder.readVaruint32();
                for (let j = 0; j < numTypes; j++) {
                    types.push(decoder.readString());
                }
                variants.push({ name, types });
            }
        }
        return new ABI({
            version,
            types,
            structs,
            actions,
            tables,
            ricardian_clauses,
            variants,
        });
    }
    toABI(encoder) {
        encoder.writeString(this.version);
        encoder.writeVaruint32(this.types.length);
        for (const type of this.types) {
            encoder.writeString(type.new_type_name);
            encoder.writeString(type.type);
        }
        encoder.writeVaruint32(this.structs.length);
        for (const struct of this.structs) {
            encoder.writeString(struct.name);
            encoder.writeString(struct.base);
            encoder.writeVaruint32(struct.fields.length);
            for (const field of struct.fields) {
                encoder.writeString(field.name);
                encoder.writeString(field.type);
            }
        }
        encoder.writeVaruint32(this.actions.length);
        for (const action of this.actions) {
            Name.from(action.name).toABI(encoder);
            encoder.writeString(action.type);
            encoder.writeString(action.ricardian_contract);
        }
        encoder.writeVaruint32(this.tables.length);
        for (const table of this.tables) {
            Name.from(table.name).toABI(encoder);
            encoder.writeString(table.index_type);
            encoder.writeVaruint32(table.key_names.length);
            for (const key of table.key_names) {
                encoder.writeString(key);
            }
            encoder.writeVaruint32(table.key_types.length);
            for (const key of table.key_types) {
                encoder.writeString(key);
            }
            encoder.writeString(table.type);
        }
        encoder.writeVaruint32(this.ricardian_clauses.length);
        for (const clause of this.ricardian_clauses) {
            encoder.writeString(clause.id);
            encoder.writeString(clause.body);
        }
        encoder.writeVaruint32(0); // error_messages
        encoder.writeVaruint32(0); // extensions
        encoder.writeVaruint32(this.variants.length);
        for (const variant of this.variants) {
            encoder.writeString(variant.name);
            encoder.writeVaruint32(variant.types.length);
            for (const type of variant.types) {
                encoder.writeString(type);
            }
        }
    }
    resolveType(name) {
        const types = {};
        return this.resolve({ name, types }, { id: 0 });
    }
    resolveAll() {
        const types = {};
        const ctx = { id: 0 };
        return {
            types: this.types.map((t) => this.resolve({ name: t.new_type_name, types }, ctx)),
            variants: this.variants.map((t) => this.resolve({ name: t.name, types }, ctx)),
            structs: this.structs.map((t) => this.resolve({ name: t.name, types }, ctx)),
        };
    }
    resolve({ name, types }, ctx) {
        const existing = types[name];
        if (existing) {
            return existing;
        }
        const type = new ABI.ResolvedType(name, ++ctx.id);
        types[type.typeName] = type;
        const alias = this.types.find((typeDef) => typeDef.new_type_name == type.name);
        if (alias) {
            type.ref = this.resolve({ name: alias.type, types }, ctx);
            return type;
        }
        const struct = this.getStruct(type.name);
        if (struct) {
            if (struct.base) {
                type.base = this.resolve({ name: struct.base, types }, ctx);
            }
            type.fields = struct.fields.map((field) => {
                return {
                    name: field.name,
                    type: this.resolve({ name: field.type, types }, ctx),
                };
            });
            return type;
        }
        const variant = this.getVariant(type.name);
        if (variant) {
            type.variant = variant.types.map((name) => this.resolve({ name, types }, ctx));
            return type;
        }
        // builtin or unknown type
        return type;
    }
    getStruct(name) {
        return this.structs.find((struct) => struct.name == name);
    }
    getVariant(name) {
        return this.variants.find((variant) => variant.name == name);
    }
    /** Return arguments type of an action in this ABI. */
    getActionType(actionName) {
        const name = Name.from(actionName).toString();
        const action = this.actions.find((a) => a.name.toString() === name);
        if (action) {
            return action.type;
        }
    }
    equals(other) {
        const o = ABI.from(other);
        if (this.version != o.version ||
            this.types.length != o.types.length ||
            this.structs.length != o.structs.length ||
            this.actions.length != o.actions.length ||
            this.tables.length != o.tables.length ||
            this.ricardian_clauses.length != o.ricardian_clauses.length ||
            this.variants.length != o.variants.length) {
            return false;
        }
        return abiEncode({ object: this }).equals(abiEncode({ object: o }));
    }
    toJSON() {
        return {
            version: this.version,
            types: this.types,
            structs: this.structs,
            actions: this.actions,
            tables: this.tables,
            ricardian_clauses: this.ricardian_clauses,
            error_messages: [],
            abi_extensions: [],
            variants: this.variants,
        };
    }
}
ABI.abiName = 'abi';
ABI.version = 'eosio::abi/1.1';
(function (ABI) {
    class ResolvedType {
        constructor(fullName, id = 0) {
            let name = fullName;
            if (name.endsWith('$')) {
                name = name.slice(0, -1);
                this.isExtension = true;
            }
            else {
                this.isExtension = false;
            }
            if (name.endsWith('?')) {
                name = name.slice(0, -1);
                this.isOptional = true;
            }
            else {
                this.isOptional = false;
            }
            if (name.endsWith('[]')) {
                name = name.slice(0, -2);
                this.isArray = true;
            }
            else {
                this.isArray = false;
            }
            this.id = id;
            this.name = name;
        }
        /**
         * Type name including suffixes: [] array, ? optional, $ binary ext
         */
        get typeName() {
            let rv = this.name;
            if (this.isArray) {
                rv += '[]';
            }
            if (this.isOptional) {
                rv += '?';
            }
            if (this.isExtension) {
                rv += '$';
            }
            return rv;
        }
        /** All fields including base struct(s), undefined if not a struct type. */
        get allFields() {
            // eslint-disable-next-line @typescript-eslint/no-this-alias
            let current = this;
            const rv = [];
            const seen = new Set();
            do {
                if (!current.fields) {
                    return; // invalid struct
                }
                if (seen.has(current.name)) {
                    return; // circular ref
                }
                for (let i = current.fields.length - 1; i >= 0; i--) {
                    rv.unshift(current.fields[i]);
                }
                seen.add(current.name);
                current = current.base;
            } while (current !== undefined);
            return rv;
        }
    }
    ABI.ResolvedType = ResolvedType;
})(ABI || (ABI = {}));

class Asset {
    constructor(units, symbol) {
        this.units = units;
        this.symbol = symbol;
    }
    static from(value, symbol) {
        if (isInstanceOf(value, Asset)) {
            return value;
        }
        switch (typeof value) {
            case 'number':
                if (!symbol) {
                    throw new Error('Symbol is required when creating Asset from number');
                }
                return this.fromFloat(value, symbol);
            case 'string':
                return this.fromString(value);
            default:
                throw new Error('Invalid asset');
        }
    }
    static fromString(value) {
        const parts = (typeof value === 'string' ? value : '').split(' ');
        if (parts.length !== 2) {
            throw new Error('Invalid asset string');
        }
        const amount = parts[0].replace('.', '');
        const precision = (parts[0].split('.')[1] || '').length;
        const symbol = Asset.Symbol.fromParts(parts[1], precision);
        return new Asset(Int64.from(amount), symbol);
    }
    static fromFloat(value, symbol) {
        const s = Asset.Symbol.from(symbol);
        return new Asset(s.convertFloat(value), s);
    }
    static fromUnits(value, symbol) {
        return new Asset(Int64.from(value), Asset.Symbol.from(symbol));
    }
    static fromABI(decoder) {
        const units = Int64.fromABI(decoder);
        const symbol = Asset.Symbol.fromABI(decoder);
        return new Asset(units, symbol);
    }
    equals(other) {
        const { symbol, units } = Asset.from(other);
        return this.symbol.value.equals(symbol.value) && this.units.equals(units);
    }
    get value() {
        return this.symbol.convertUnits(this.units);
    }
    set value(newValue) {
        this.units = this.symbol.convertFloat(newValue);
    }
    toABI(encoder) {
        this.units.toABI(encoder);
        this.symbol.toABI(encoder);
    }
    toString() {
        const digits = this.units.toString().split('');
        let negative = false;
        if (digits[0] === '-') {
            negative = true;
            digits.shift();
        }
        const p = this.symbol.precision;
        while (digits.length <= p) {
            digits.unshift('0');
        }
        if (p > 0) {
            digits.splice(digits.length - p, 0, '.');
        }
        let rv = digits.join('');
        if (negative) {
            rv = '-' + rv;
        }
        return rv + ' ' + this.symbol.name;
    }
    toJSON() {
        return this.toString();
    }
}
Asset.abiName = 'asset';
(function (Asset) {
    class Symbol {
        constructor(value) {
            if (toSymbolPrecision(value) > Symbol.maxPrecision) {
                throw new Error('Invalid asset symbol, precision too large');
            }
            if (!Symbol.symbolNamePattern.test(toSymbolName(value))) {
                throw new Error('Invalid asset symbol, name must be uppercase A-Z');
            }
            this.value = value;
        }
        static from(value) {
            if (isInstanceOf(value, Symbol)) {
                return value;
            }
            if (isInstanceOf(value, UInt64)) {
                return new Symbol(value);
            }
            const parts = value.split(',');
            if (parts.length !== 2) {
                throw new Error('Invalid symbol string');
            }
            const precision = Number.parseInt(parts[0]);
            return Symbol.fromParts(parts[1], precision);
        }
        static fromParts(name, precision) {
            return new Symbol(toRawSymbol(name, precision));
        }
        // eslint-disable-next-line @typescript-eslint/ban-types
        static fromABI(decoder) {
            return new Symbol(UInt64.fromABI(decoder));
        }
        equals(other) {
            return this.value.equals(Symbol.from(other).value);
        }
        get name() {
            return toSymbolName(this.value);
        }
        get precision() {
            return toSymbolPrecision(this.value);
        }
        get code() {
            return new SymbolCode(UInt64.from(this.value.value.clone().iushrn(8)));
        }
        toABI(encoder) {
            this.value.toABI(encoder);
        }
        /**
         * Convert units to floating point number according to symbol precision.
         * @throws If the given units can't be represented in 53 bits.
         **/
        convertUnits(units) {
            return units.value.toNumber() / Math.pow(10, this.precision);
        }
        /**
         * Convert floating point to units according to symbol precision.
         * Note that the value will be rounded to closest precision.
         **/
        convertFloat(float) {
            return Int64.from(float.toFixed(this.precision).replace('.', ''));
        }
        toString() {
            return `${this.precision},${this.name}`;
        }
        toJSON() {
            return this.toString();
        }
    }
    Symbol.abiName = 'symbol';
    Symbol.symbolNamePattern = /^[A-Z]{1,7}$/;
    Symbol.maxPrecision = 18;
    Asset.Symbol = Symbol;
    class SymbolCode {
        constructor(value) {
            this.value = value;
        }
        static from(value) {
            if (isInstanceOf(value, SymbolCode)) {
                return value;
            }
            if (typeof value === 'string') {
                value = UInt64.from(toRawSymbolCode(value));
            }
            return new this(UInt64.from(value));
        }
        static fromABI(decoder) {
            return new SymbolCode(UInt64.fromABI(decoder));
        }
        equals(other) {
            return this.value.equals(SymbolCode.from(other).value);
        }
        toABI(encoder) {
            this.value.toABI(encoder);
        }
        toString() {
            return charsToSymbolName(this.value.value.toArray('be'));
        }
        toJSON() {
            return this.toString();
        }
    }
    SymbolCode.abiName = 'symbol_code';
    Asset.SymbolCode = SymbolCode;
})(Asset || (Asset = {}));
class ExtendedAsset {
    constructor(quantity, contract) {
        this.quantity = quantity;
        this.contract = contract;
    }
    static from(value) {
        if (isInstanceOf(value, ExtendedAsset)) {
            return value;
        }
        return new this(Asset.from(value.quantity), Name.from(value.contract));
    }
    static fromABI(decoder) {
        return new ExtendedAsset(Asset.fromABI(decoder), Name.fromABI(decoder));
    }
    equals(other) {
        return this.quantity.equals(other.quantity) && this.contract.equals(other.contract);
    }
    toABI(encoder) {
        this.quantity.toABI(encoder);
        this.contract.toABI(encoder);
    }
    toJSON() {
        return {
            quantity: this.quantity,
            contract: this.contract,
        };
    }
}
ExtendedAsset.abiName = 'extended_asset';
function toSymbolPrecision(rawSymbol) {
    return rawSymbol.value.and(UInt64.from(0xff).value).toNumber();
}
function toSymbolName(rawSymbol) {
    const chars = rawSymbol.value.toArray('be').slice(0, -1);
    return charsToSymbolName(chars);
}
function charsToSymbolName(chars) {
    return chars
        .map((char) => String.fromCharCode(char))
        .reverse()
        .join('');
}
function toRawSymbol(name, precision) {
    const code = toRawSymbolCode(name);
    const bytes = new Uint8Array(code.length + 1);
    bytes[0] = precision;
    bytes.set(code, 1);
    return UInt64.from(bytes);
}
function toRawSymbolCode(name) {
    const length = Math.min(name.length, 7);
    const bytes = new Uint8Array(length);
    for (let i = 0; i < length; i++) {
        bytes[i] = name.charCodeAt(i);
    }
    return bytes;
}

var Base58;
(function (Base58) {
    let ErrorCode;
    (function (ErrorCode) {
        ErrorCode["E_CHECKSUM"] = "E_CHECKSUM";
        ErrorCode["E_INVALID"] = "E_INVALID";
    })(ErrorCode = Base58.ErrorCode || (Base58.ErrorCode = {}));
    class DecodingError extends Error {
        constructor(message, code, info = {}) {
            super(message);
            this.code = code;
            this.info = info;
        }
    }
    DecodingError.__className = 'DecodingError';
    Base58.DecodingError = DecodingError;
    const chars = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
    const charMap = new Int16Array(0xff).fill(-1);
    for (let i = 0; i < 58; ++i) {
        charMap[chars.charCodeAt(i)] = i;
    }
    /** Decode a Base58 encoded string. */
    function decode(s, size) {
        if (size == null) {
            return decodeVar(s);
        }
        const result = new Uint8Array(size);
        for (let i = 0; i < s.length; ++i) {
            let carry = charMap[s.charCodeAt(i)];
            if (carry < 0) {
                throw new DecodingError('Invalid Base58 character encountered', ErrorCode.E_INVALID, { char: s[i] });
            }
            for (let j = 0; j < size; ++j) {
                const x = result[j] * 58 + carry;
                result[j] = x;
                carry = x >> 8;
            }
            if (carry) {
                throw new DecodingError('Base58 value is out of range', ErrorCode.E_INVALID);
            }
        }
        result.reverse();
        return new Bytes(result);
    }
    Base58.decode = decode;
    /** Decode a Base58Check encoded string. */
    function decodeCheck(encoded, size) {
        const decoded = decode(encoded, size != null ? size + 4 : size);
        const data = decoded.array.subarray(0, -4);
        const expected = decoded.array.subarray(-4);
        const actual = dsha256Checksum(data);
        if (!arrayEquals(expected, actual)) {
            throw new DecodingError('Checksum mismatch', ErrorCode.E_CHECKSUM, {
                actual,
                expected,
                data,
                hash: 'double_sha256',
            });
        }
        return new Bytes(data);
    }
    Base58.decodeCheck = decodeCheck;
    /** Decode a Base58Check encoded string that uses ripemd160 instead of double sha256 for the digest. */
    function decodeRipemd160Check(encoded, size, suffix) {
        const decoded = decode(encoded, size != null ? size + 4 : size);
        const data = decoded.array.subarray(0, -4);
        const expected = decoded.array.subarray(-4);
        const actual = ripemd160Checksum(data, suffix);
        if (!arrayEquals(expected, actual)) {
            throw new DecodingError('Checksum mismatch', ErrorCode.E_CHECKSUM, {
                actual,
                expected,
                data,
                hash: 'ripemd160',
            });
        }
        return new Bytes(data);
    }
    Base58.decodeRipemd160Check = decodeRipemd160Check;
    /** Encode bytes to a Base58 string.  */
    function encode(data) {
        data = Bytes.from(data);
        const result = [];
        for (const byte of data.array) {
            let carry = byte;
            for (let j = 0; j < result.length; ++j) {
                const x = (charMap[result[j]] << 8) + carry;
                result[j] = chars.charCodeAt(x % 58);
                carry = (x / 58) | 0;
            }
            while (carry) {
                result.push(chars.charCodeAt(carry % 58));
                carry = (carry / 58) | 0;
            }
        }
        for (const byte of data.array) {
            if (byte) {
                break;
            }
            else {
                result.push('1'.charCodeAt(0));
            }
        }
        result.reverse();
        return String.fromCharCode(...result);
    }
    Base58.encode = encode;
    function encodeCheck(data) {
        data = Bytes.from(data);
        data = data.appending(dsha256Checksum(data.array));
        return encode(data);
    }
    Base58.encodeCheck = encodeCheck;
    function encodeRipemd160Check(data, suffix) {
        data = Bytes.from(data);
        data = data.appending(ripemd160Checksum(data.array, suffix));
        return encode(data);
    }
    Base58.encodeRipemd160Check = encodeRipemd160Check;
    /** @internal */
    function decodeVar(s) {
        const result = [];
        for (let i = 0; i < s.length; ++i) {
            let carry = charMap[s.charCodeAt(i)];
            if (carry < 0) {
                throw new DecodingError('Invalid Base58 character encountered', ErrorCode.E_INVALID, { char: s[i] });
            }
            for (let j = 0; j < result.length; ++j) {
                const x = result[j] * 58 + carry;
                result[j] = x & 0xff;
                carry = x >> 8;
            }
            if (carry) {
                result.push(carry);
            }
        }
        for (const ch of s) {
            if (ch === '1') {
                result.push(0);
            }
            else {
                break;
            }
        }
        result.reverse();
        return Bytes.from(result);
    }
    /** @internal */
    function ripemd160Checksum(data, suffix) {
        const hash = ripemd160().update(data);
        if (suffix) {
            hash.update(suffix);
        }
        return new Uint8Array(hash.digest().slice(0, 4));
    }
    /** @internal */
    function dsha256Checksum(data) {
        const round1 = sha256().update(data).digest();
        const round2 = sha256().update(round1).digest();
        return new Uint8Array(round2.slice(0, 4));
    }
})(Base58 || (Base58 = {}));

class PublicKey {
    /** @internal */
    constructor(type, data) {
        this.type = type;
        this.data = data;
    }
    /** Create PublicKey object from representing types. */
    static from(value) {
        if (isInstanceOf(value, PublicKey)) {
            return value;
        }
        if (typeof value === 'object' && value.type && value.compressed) {
            return new PublicKey(KeyType.from(value.type), new Bytes(value.compressed));
        }
        if (typeof value !== 'string') {
            throw new Error('Invalid public key');
        }
        if (value.startsWith('PUB_')) {
            const parts = value.split('_');
            if (parts.length !== 3) {
                throw new Error('Invalid public key string');
            }
            const type = KeyType.from(parts[1]);
            const size = type === KeyType.K1 || type === KeyType.R1 ? 33 : undefined;
            const data = Base58.decodeRipemd160Check(parts[2], size, type);
            return new PublicKey(type, data);
        }
        else if (value.length >= 50) {
            // Legacy EOS key
            const data = Base58.decodeRipemd160Check(value.slice(-50));
            return new PublicKey(KeyType.K1, data);
        }
        else {
            throw new Error('Invalid public key string');
        }
    }
    /** @internal */
    static fromABI(decoder) {
        const type = KeyType.from(decoder.readByte());
        if (type == KeyType.WA) {
            const startPos = decoder.getPosition();
            decoder.advance(33); // key_data
            decoder.advance(1); // user presence
            decoder.advance(decoder.readVaruint32()); // rpid
            const len = decoder.getPosition() - startPos;
            decoder.setPosition(startPos);
            const data = Bytes.from(decoder.readArray(len));
            return new PublicKey(KeyType.WA, data);
        }
        return new PublicKey(type, new Bytes(decoder.readArray(33)));
    }
    equals(other) {
        const otherKey = PublicKey.from(other);
        return this.type === otherKey.type && this.data.equals(otherKey.data);
    }
    /**
     * Return EOSIO legacy (`EOS<base58data>`) formatted key.
     * @throws If the key type isn't `K1`
     */
    toLegacyString(prefix = 'EOS') {
        if (this.type !== KeyType.K1) {
            throw new Error('Unable to create legacy formatted string for non-K1 key');
        }
        return `${prefix}${Base58.encodeRipemd160Check(this.data)}`;
    }
    /** Return key in modern EOSIO format (`PUB_<type>_<base58data>`) */
    toString() {
        return `PUB_${this.type}_${Base58.encodeRipemd160Check(this.data, this.type)}`;
    }
    /** @internal */
    toABI(encoder) {
        encoder.writeByte(KeyType.indexFor(this.type));
        encoder.writeArray(this.data.array);
    }
    /** @internal */
    toJSON() {
        return this.toString();
    }
}
PublicKey.abiName = 'public_key';

const curves = {};
/**
 * Get curve for key type.
 * @internal
 */
function getCurve(type) {
    let rv = curves[type];
    if (!rv) {
        if (type === 'K1') {
            rv = curves[type] = new ec('secp256k1');
        }
        else if (type === 'R1') {
            rv = curves[type] = new ec('p256');
        }
        else {
            throw new Error(`Unknown curve type: ${type}`);
        }
    }
    return rv;
}

/**
 * Recover public key from signature and recovery id.
 * @internal
 */
function recover(signature, message, type) {
    const curve = getCurve(type);
    const recid = signature[0] - 31;
    const r = signature.subarray(1, 33);
    const s = signature.subarray(33);
    const point = curve.recoverPubKey(message, { r, s }, recid);
    return new Uint8Array(point.encodeCompressed());
}

/**
 * Verify signature using message and public key.
 * @internal
 */
function verify(signature, message, pubkey, type) {
    const curve = getCurve(type);
    const r = signature.subarray(1, 33);
    const s = signature.subarray(33);
    return curve.verify(message, { r, s }, pubkey);
}

class Signature {
    /** @internal */
    constructor(type, data) {
        this.type = type;
        this.data = data;
    }
    /** Create Signature object from representing types. */
    static from(value) {
        if (isInstanceOf(value, Signature)) {
            return value;
        }
        if (typeof value === 'object' && value.r && value.s) {
            const data = new Uint8Array(1 + 32 + 32);
            let recid = value.recid;
            const type = KeyType.from(value.type);
            if (value.type === KeyType.K1 || value.type === KeyType.R1) {
                recid += 31;
            }
            data[0] = recid;
            data.set(value.r, 1);
            data.set(value.s, 33);
            return new Signature(type, new Bytes(data));
        }
        if (typeof value !== 'string') {
            throw new Error('Invalid signature');
        }
        if (value.startsWith('SIG_')) {
            const parts = value.split('_');
            if (parts.length !== 3) {
                throw new Error('Invalid signature string');
            }
            const type = KeyType.from(parts[1]);
            const size = type === KeyType.K1 || type === KeyType.R1 ? 65 : undefined;
            const data = Base58.decodeRipemd160Check(parts[2], size, type);
            return new Signature(type, data);
        }
        else {
            throw new Error('Invalid signature string');
        }
    }
    /** @internal */
    static fromABI(decoder) {
        const type = KeyType.from(decoder.readByte());
        if (type === KeyType.WA) {
            const startPos = decoder.getPosition();
            decoder.advance(65); // compact_signature
            decoder.advance(decoder.readVaruint32()); // auth_data
            decoder.advance(decoder.readVaruint32()); // client_json
            const len = decoder.getPosition() - startPos;
            decoder.setPosition(startPos);
            const data = Bytes.from(decoder.readArray(len));
            return new Signature(KeyType.WA, data);
        }
        return new Signature(type, new Bytes(decoder.readArray(65)));
    }
    equals(other) {
        const otherSig = Signature.from(other);
        return this.type === otherSig.type && this.data.equals(otherSig.data);
    }
    /** Recover public key from given message digest. */
    recoverDigest(digest) {
        digest = Checksum256.from(digest);
        const compressed = recover(this.data.array, digest.array, this.type);
        return PublicKey.from({ compressed, type: this.type });
    }
    /** Recover public key from given message. */
    recoverMessage(message) {
        return this.recoverDigest(Checksum256.hash(message));
    }
    /** Verify this signature with given message digest and public key. */
    verifyDigest(digest, publicKey) {
        digest = Checksum256.from(digest);
        return verify(this.data.array, digest.array, publicKey.data.array, this.type);
    }
    /** Verify this signature with given message and public key. */
    verifyMessage(message, publicKey) {
        return this.verifyDigest(Checksum256.hash(message), publicKey);
    }
    /** Base58check encoded string representation of this signature (`SIG_<type>_<data>`). */
    toString() {
        return `SIG_${this.type}_${Base58.encodeRipemd160Check(this.data, this.type)}`;
    }
    /** @internal */
    toABI(encoder) {
        encoder.writeByte(KeyType.indexFor(this.type));
        encoder.writeArray(this.data.array);
    }
    /** @internal */
    toJSON() {
        return this.toString();
    }
}
Signature.abiName = 'signature';

/**
 * Get public key corresponding to given private key.
 * @internal
 */
function getPublic(privkey, type) {
    const curve = getCurve(type);
    const key = curve.keyFromPrivate(privkey);
    const point = key.getPublic();
    return new Uint8Array(point.encodeCompressed());
}

/**
 * Derive shared secret for key pair.
 * @internal
 */
function sharedSecret(privkey, pubkey, type) {
    const curve = getCurve(type);
    const priv = curve.keyFromPrivate(privkey);
    const pub = curve.keyFromPublic(pubkey).getPublic();
    return priv.derive(pub).toArrayLike(Uint8Array, 'be');
}

/**
 * Sign digest using private key.
 * @internal
 */
function sign(secret, message, type) {
    const curve = getCurve(type);
    const key = curve.keyFromPrivate(secret);
    let sig;
    let r;
    let s;
    if (type === 'K1') {
        let attempt = 1;
        do {
            sig = key.sign(message, { canonical: true, pers: [attempt++] });
            r = sig.r.toArrayLike(Uint8Array, 'be', 32);
            s = sig.s.toArrayLike(Uint8Array, 'be', 32);
        } while (!isCanonical(r, s));
    }
    else {
        sig = key.sign(message, { canonical: true });
        r = sig.r.toArrayLike(Uint8Array, 'be', 32);
        s = sig.s.toArrayLike(Uint8Array, 'be', 32);
    }
    return { type, r, s, recid: sig.recoveryParam || 0 };
}
/**
 * Here be dragons
 * - https://github.com/steemit/steem/issues/1944
 * - https://github.com/EOSIO/eos/issues/6699
 * @internal
 */
function isCanonical(r, s) {
    return (!(r[0] & 0x80) &&
        !(r[0] === 0 && !(r[1] & 0x80)) &&
        !(s[0] & 0x80) &&
        !(s[0] === 0 && !(s[1] & 0x80)));
}

/**
 * Generate a new private key for given type.
 * @internal
 */
function generate(type) {
    const curve = getCurve(type);
    const privkey = curve.genKeyPair().getPrivate();
    return privkey.toArrayLike(Uint8Array, 'be');
}

class PrivateKey {
    /** @internal */
    constructor(type, data) {
        this.type = type;
        this.data = data;
    }
    /** Create PrivateKey object from representing types. */
    static from(value) {
        if (isInstanceOf(value, PrivateKey)) {
            return value;
        }
        else {
            return this.fromString(value);
        }
    }
    /**
     * Create PrivateKey object from a string representation.
     * Accepts WIF (5...) and EOSIO (PVT_...) style private keys.
     */
    static fromString(string, ignoreChecksumError = false) {
        try {
            const { type, data } = decodeKey(string);
            return new this(type, data);
        }
        catch (error) {
            error.message = `Invalid private key (${error.message})`;
            if (ignoreChecksumError &&
                isInstanceOf(error, Base58.DecodingError) &&
                error.code === Base58.ErrorCode.E_CHECKSUM) {
                const type = string.startsWith('PVT_R1') ? KeyType.R1 : KeyType.K1;
                let data = new Bytes(error.info.data);
                if (data.array.length == 33) {
                    data = data.droppingFirst();
                }
                return new this(type, data);
            }
            throw error;
        }
    }
    /**
     * Generate new PrivateKey.
     * @throws If a secure random source isn't available.
     */
    static generate(type) {
        return new PrivateKey(KeyType.from(type), new Bytes(generate(type)));
    }
    /**
     * Sign message digest using this key.
     * @throws If the key type isn't R1 or K1.
     */
    signDigest(digest) {
        digest = Checksum256.from(digest);
        return Signature.from(sign(this.data.array, digest.array, this.type));
    }
    /**
     * Sign message using this key.
     * @throws If the key type isn't R1 or K1.
     */
    signMessage(message) {
        return this.signDigest(Checksum256.hash(message));
    }
    /**
     * Derive the shared secret between this private key and given public key.
     * @throws If the key type isn't R1 or K1.
     */
    sharedSecret(publicKey) {
        const shared = sharedSecret(this.data.array, publicKey.data.array, this.type);
        return Checksum512.hash(shared);
    }
    /**
     * Get the corresponding public key.
     * @throws If the key type isn't R1 or K1.
     */
    toPublic() {
        const compressed = getPublic(this.data.array, this.type);
        return PublicKey.from({ compressed, type: this.type });
    }
    /**
     * Return WIF representation of this private key
     * @throws If the key type isn't K1.
     */
    toWif() {
        if (this.type !== KeyType.K1) {
            throw new Error('Unable to generate WIF for non-k1 key');
        }
        return Base58.encodeCheck(Bytes.from([0x80]).appending(this.data));
    }
    /**
     * Return the key in EOSIO PVT_<type>_<base58check> format.
     */
    toString() {
        return `PVT_${this.type}_${Base58.encodeRipemd160Check(this.data, this.type)}`;
    }
    toJSON() {
        return this.toString();
    }
}
/** @internal */
function decodeKey(value) {
    const type = typeof value;
    if (type !== 'string') {
        throw new Error(`Expected string, got ${type}`);
    }
    if (value.startsWith('PVT_')) {
        // EOSIO format
        const parts = value.split('_');
        if (parts.length !== 3) {
            throw new Error('Invalid PVT format');
        }
        const type = KeyType.from(parts[1]);
        let size;
        switch (type) {
            case KeyType.K1:
            case KeyType.R1:
                size = 32;
                break;
        }
        const data = Base58.decodeRipemd160Check(parts[2], size, type);
        return { type, data };
    }
    else {
        // WIF format
        const type = KeyType.K1;
        const data = Base58.decodeCheck(value);
        if (data.array[0] !== 0x80) {
            throw new Error('Invalid WIF');
        }
        return { type, data: data.droppingFirst() };
    }
}

var PermissionLevel_1;
/** EOSIO Permission Level, a.k.a "auth". */
let PermissionLevel = PermissionLevel_1 = class PermissionLevel extends Struct {
    /** Create new permission level from representing types. Can be expressed as a string in the format `<actor>@<permission>`. */
    static from(value) {
        if (typeof value === 'string') {
            const parts = value.split('@');
            if (parts.length !== 2 && parts[0].length > 0 && parts[1].length > 0) {
                throw new Error('Invalid permission level string, should be in the format <actor>@<permission>');
            }
            value = { actor: parts[0], permission: parts[1] };
        }
        return super.from(value);
    }
    /** Return true if this permission level equals other. */
    equals(other) {
        const otherPerm = PermissionLevel_1.from(other);
        return this.actor.equals(otherPerm.actor) && this.permission.equals(otherPerm.permission);
    }
    toString() {
        return `${this.actor}@${this.permission}`;
    }
};
__decorate([
    Struct.field('name')
], PermissionLevel.prototype, "actor", void 0);
__decorate([
    Struct.field('name')
], PermissionLevel.prototype, "permission", void 0);
PermissionLevel = PermissionLevel_1 = __decorate([
    Struct.type('permission_level')
], PermissionLevel);

var Action_1;
let Action = Action_1 = class Action extends Struct {
    static from(object, abi) {
        const data = object.data;
        if (!Bytes.isBytes(data)) {
            let type;
            if (abi) {
                type = ABI.from(abi).getActionType(object.name);
            }
            else if (!data.constructor || data.constructor.abiName === undefined) {
                throw new Error('Missing ABI definition when creating action with untyped action data');
            }
            object = {
                ...object,
                data: abiEncode({ object: data, type, abi }),
            };
        }
        return super.from(object);
    }
    /** Return true if this Action is equal to given action. */
    equals(other) {
        const otherAction = Action_1.from(other);
        return (this.account.equals(otherAction.account) &&
            this.name.equals(otherAction.name) &&
            arrayEquatableEquals(this.authorization, otherAction.authorization) &&
            this.data.equals(otherAction.data));
    }
    decodeData(typeOrAbi) {
        if (typeof typeOrAbi === 'string' || typeOrAbi.abiName) {
            return abiDecode({
                data: this.data,
                type: typeOrAbi,
            });
        }
        else {
            const abi = ABI.from(typeOrAbi);
            const type = abi.getActionType(this.name);
            if (!type) {
                throw new Error(`Action ${this.name} does not exist in provided ABI`);
            }
            return abiDecode({ data: this.data, type, abi });
        }
    }
};
__decorate([
    Struct.field('name')
], Action.prototype, "account", void 0);
__decorate([
    Struct.field('name')
], Action.prototype, "name", void 0);
__decorate([
    Struct.field(PermissionLevel, { array: true })
], Action.prototype, "authorization", void 0);
__decorate([
    Struct.field('bytes')
], Action.prototype, "data", void 0);
Action = Action_1 = __decorate([
    Struct.type('action')
], Action);

var Transaction_1;
let TransactionExtension = class TransactionExtension extends Struct {
};
__decorate([
    Struct.field('uint16')
], TransactionExtension.prototype, "type", void 0);
__decorate([
    Struct.field('bytes')
], TransactionExtension.prototype, "data", void 0);
TransactionExtension = __decorate([
    Struct.type('transaction_extension')
], TransactionExtension);
let TransactionHeader = class TransactionHeader extends Struct {
    static from(object) {
        return super.from(object);
    }
};
__decorate([
    Struct.field('time_point_sec')
], TransactionHeader.prototype, "expiration", void 0);
__decorate([
    Struct.field('uint16')
], TransactionHeader.prototype, "ref_block_num", void 0);
__decorate([
    Struct.field('uint32')
], TransactionHeader.prototype, "ref_block_prefix", void 0);
__decorate([
    Struct.field('varuint32', { default: 0 })
], TransactionHeader.prototype, "max_net_usage_words", void 0);
__decorate([
    Struct.field('uint8', { default: 0 })
], TransactionHeader.prototype, "max_cpu_usage_ms", void 0);
__decorate([
    Struct.field('varuint32', { default: 0 })
], TransactionHeader.prototype, "delay_sec", void 0);
TransactionHeader = __decorate([
    Struct.type('transaction_header')
], TransactionHeader);
let Transaction = Transaction_1 = class Transaction extends TransactionHeader {
    static from(object, abis) {
        const abiFor = (contract) => {
            if (!abis) {
                return;
            }
            else if (Array.isArray(abis)) {
                return abis
                    .filter((abi) => Name.from(abi.contract).equals(contract))
                    .map(({ abi }) => abi)[0];
            }
            else {
                return abis;
            }
        };
        const resolveAction = (action) => Action.from(action, abiFor(action.account));
        const actions = (object.actions || []).map(resolveAction);
        const context_free_actions = (object.context_free_actions || []).map(resolveAction);
        const transaction = {
            ...object,
            context_free_actions,
            actions,
        };
        return super.from(transaction);
    }
    /** Return true if this transaction is equal to given transaction. */
    equals(other) {
        const tx = Transaction_1.from(other);
        return this.id.equals(tx.id);
    }
    get id() {
        return Checksum256.hash(abiEncode({ object: this }));
    }
    signingDigest(chainId) {
        const data = this.signingData(chainId);
        return Checksum256.hash(data);
    }
    signingData(chainId) {
        let data = Bytes.from(Checksum256.from(chainId).array);
        data = data.appending(abiEncode({ object: this }));
        data = data.appending(new Uint8Array(32));
        return data;
    }
};
__decorate([
    Struct.field(Action, { array: true, default: [] })
], Transaction.prototype, "context_free_actions", void 0);
__decorate([
    Struct.field(Action, { array: true, default: [] })
], Transaction.prototype, "actions", void 0);
__decorate([
    Struct.field(TransactionExtension, { array: true, default: [] })
], Transaction.prototype, "transaction_extensions", void 0);
Transaction = Transaction_1 = __decorate([
    Struct.type('transaction')
], Transaction);
let SignedTransaction = class SignedTransaction extends Transaction {
    static from(object) {
        return super.from(object);
    }
};
__decorate([
    Struct.field('signature[]', { default: [] })
], SignedTransaction.prototype, "signatures", void 0);
__decorate([
    Struct.field('bytes[]', { default: [] })
], SignedTransaction.prototype, "context_free_data", void 0);
SignedTransaction = __decorate([
    Struct.type('signed_transaction')
], SignedTransaction);
let PackedTransaction = class PackedTransaction extends Struct {
    static fromSigned(signed) {
        const tx = Transaction.from(signed);
        return this.from({
            signatures: signed.signatures,
            packed_context_free_data: abiEncode({
                object: signed.context_free_data,
                type: 'bytes[]',
            }),
            packed_trx: abiEncode({ object: tx }),
        });
    }
    getTransaction() {
        if (Number(this.compression) !== 0) {
            throw new Error('Transaction compression not supported yet');
        }
        return abiDecode({ data: this.packed_trx, type: Transaction });
    }
    getSignedTransaction() {
        const transaction = this.getTransaction();
        // TODO: decode context free data
        return SignedTransaction.from({
            ...transaction,
            signatures: this.signatures,
        });
    }
};
__decorate([
    Struct.field('signature[]')
], PackedTransaction.prototype, "signatures", void 0);
__decorate([
    Struct.field('uint8', { default: 0 })
], PackedTransaction.prototype, "compression", void 0);
__decorate([
    Struct.field('bytes')
], PackedTransaction.prototype, "packed_context_free_data", void 0);
__decorate([
    Struct.field('bytes')
], PackedTransaction.prototype, "packed_trx", void 0);
PackedTransaction = __decorate([
    Struct.type('packed_transaction')
], PackedTransaction);
let TransactionReceipt = class TransactionReceipt extends Struct {
};
__decorate([
    Struct.field('string')
], TransactionReceipt.prototype, "status", void 0);
__decorate([
    Struct.field('uint32')
], TransactionReceipt.prototype, "cpu_usage_us", void 0);
__decorate([
    Struct.field('uint32')
], TransactionReceipt.prototype, "net_usage_words", void 0);
TransactionReceipt = __decorate([
    Struct.type('transaction_receipt')
], TransactionReceipt);

var Authority_1;
let Weight = class Weight extends UInt16 {
};
Weight = __decorate([
    TypeAlias('weight_type')
], Weight);
let KeyWeight = class KeyWeight extends Struct {
};
__decorate([
    Struct.field(PublicKey)
], KeyWeight.prototype, "key", void 0);
__decorate([
    Struct.field(Weight)
], KeyWeight.prototype, "weight", void 0);
KeyWeight = __decorate([
    Struct.type('key_weight')
], KeyWeight);
let PermissionLevelWeight = class PermissionLevelWeight extends Struct {
};
__decorate([
    Struct.field(PermissionLevel)
], PermissionLevelWeight.prototype, "permission", void 0);
__decorate([
    Struct.field(Weight)
], PermissionLevelWeight.prototype, "weight", void 0);
PermissionLevelWeight = __decorate([
    Struct.type('permission_level_weight')
], PermissionLevelWeight);
let WaitWeight = class WaitWeight extends Struct {
};
__decorate([
    Struct.field(UInt32)
], WaitWeight.prototype, "wait_sec", void 0);
__decorate([
    Struct.field(Weight)
], WaitWeight.prototype, "weight", void 0);
WaitWeight = __decorate([
    Struct.type('wait_weight')
], WaitWeight);
let Authority = Authority_1 = class Authority extends Struct {
    static from(value) {
        if (isInstanceOf(value, Authority_1)) {
            return value;
        }
        const rv = super.from({
            keys: [],
            accounts: [],
            waits: [],
            ...value,
        });
        rv.sort();
        return rv;
    }
    /** Total weight of all waits. */
    get waitThreshold() {
        return this.waits.reduce((val, wait) => val + wait.weight.toNumber(), 0);
    }
    /** Weight a key needs to sign for this authority. */
    get keyThreshold() {
        return this.threshold.toNumber() - this.waitThreshold;
    }
    /** Return the weight for given public key, or zero if it is not included in this authority. */
    keyWeight(publicKey) {
        const weight = this.keys.find(({ key }) => key.equals(publicKey));
        return weight ? weight.weight.toNumber() : 0;
    }
    /**
     * Check if given public key has permission in this authority,
     * @attention Does not take indirect permissions for the key via account weights into account.
     * @param publicKey The key to check.
     * @param includePartial Whether to consider auths where the key is included but can't be reached alone (e.g. multisig).
     */
    hasPermission(publicKey, includePartial = false) {
        const threshold = includePartial ? 1 : this.keyThreshold;
        const weight = this.keyWeight(publicKey);
        return weight >= threshold;
    }
    /**
     * Sorts the authority weights in place, should be called before including the authority in a `updateauth` action or it might be rejected.
     */
    sort() {
        // This hack satisfies the constraints that authority weights, see: https://github.com/greymass/eosio-core/issues/8
        this.keys.sort((a, b) => String(a.key).localeCompare(String(b.key)));
        this.accounts.sort((a, b) => String(a.permission).localeCompare(String(b.permission)));
        this.waits.sort((a, b) => String(a.wait_sec).localeCompare(String(b.wait_sec)));
    }
};
__decorate([
    Struct.field(UInt32)
], Authority.prototype, "threshold", void 0);
__decorate([
    Struct.field(KeyWeight, { array: true })
], Authority.prototype, "keys", void 0);
__decorate([
    Struct.field(PermissionLevelWeight, { array: true })
], Authority.prototype, "accounts", void 0);
__decorate([
    Struct.field(WaitWeight, { array: true })
], Authority.prototype, "waits", void 0);
Authority = Authority_1 = __decorate([
    Struct.type('authority')
], Authority);

var Serializer;
(function (Serializer) {
    Serializer.encode = abiEncode;
    Serializer.decode = abiDecode;
    /** Create an EOSIO ABI definition for given core type. */
    function synthesize(type) {
        return synthesizeABI(type).abi;
    }
    Serializer.synthesize = synthesize;
    /** Create JSON representation of a core object. */
    function stringify(object) {
        return JSON.stringify(object);
    }
    Serializer.stringify = stringify;
    /** Create a vanilla js representation of a core object. */
    function objectify(object) {
        const walk = (v) => {
            switch (typeof v) {
                case 'boolean':
                case 'number':
                case 'string':
                    return v;
                case 'object': {
                    if (v === null) {
                        return v;
                    }
                    if (typeof v.toJSON === 'function') {
                        return walk(v.toJSON());
                    }
                    if (Array.isArray(v)) {
                        return v.map(walk);
                    }
                    const rv = {};
                    for (const key of Object.keys(v)) {
                        rv[key] = walk(v[key]);
                    }
                    return rv;
                }
            }
        };
        return walk(object);
    }
    Serializer.objectify = objectify;
})(Serializer || (Serializer = {}));

/** Default provider that uses the Fetch API to call a single node. */
class FetchProvider {
    constructor(url, options = {}) {
        url = url.trim();
        if (url.endsWith('/'))
            url = url.slice(0, -1);
        this.url = url;
        if (!options.fetch) {
            if (typeof window !== 'undefined' && window.fetch) {
                this.fetch = window.fetch.bind(window);
            }
            else if (typeof global !== 'undefined' && global.fetch) {
                this.fetch = global.fetch.bind(global);
            }
            else {
                throw new Error('Missing fetch');
            }
        }
        else {
            this.fetch = options.fetch;
        }
    }
    async call(path, params) {
        const url = this.url + path;
        const response = await this.fetch(url, {
            method: 'POST',
            body: params !== undefined ? JSON.stringify(params) : undefined,
        });
        const text = await response.text();
        let json;
        try {
            json = JSON.parse(text);
        }
        catch {
            // ignore json parse errors
        }
        const headers = {};
        for (const [key, value] of response.headers.entries()) {
            headers[key] = value;
        }
        return { headers, status: response.status, json, text };
    }
}

let AccountPermission = class AccountPermission extends Struct {
};
__decorate([
    Struct.field('name')
], AccountPermission.prototype, "perm_name", void 0);
__decorate([
    Struct.field('name')
], AccountPermission.prototype, "parent", void 0);
__decorate([
    Struct.field(Authority)
], AccountPermission.prototype, "required_auth", void 0);
AccountPermission = __decorate([
    Struct.type('account_permission')
], AccountPermission);
let AccountResourceLimit = class AccountResourceLimit extends Struct {
};
__decorate([
    Struct.field('int64')
], AccountResourceLimit.prototype, "used", void 0);
__decorate([
    Struct.field('int64')
], AccountResourceLimit.prototype, "available", void 0);
__decorate([
    Struct.field('int64')
], AccountResourceLimit.prototype, "max", void 0);
AccountResourceLimit = __decorate([
    Struct.type('account_resource_limit')
], AccountResourceLimit);
let AccountTotalResources = class AccountTotalResources extends Struct {
};
__decorate([
    Struct.field('name')
], AccountTotalResources.prototype, "owner", void 0);
__decorate([
    Struct.field('asset')
], AccountTotalResources.prototype, "net_weight", void 0);
__decorate([
    Struct.field('asset')
], AccountTotalResources.prototype, "cpu_weight", void 0);
__decorate([
    Struct.field('uint64')
], AccountTotalResources.prototype, "ram_bytes", void 0);
AccountTotalResources = __decorate([
    Struct.type('account_total_resources')
], AccountTotalResources);
let AccountSelfDelegatedBandwidth = class AccountSelfDelegatedBandwidth extends Struct {
};
__decorate([
    Struct.field('name')
], AccountSelfDelegatedBandwidth.prototype, "from", void 0);
__decorate([
    Struct.field('name')
], AccountSelfDelegatedBandwidth.prototype, "to", void 0);
__decorate([
    Struct.field('asset')
], AccountSelfDelegatedBandwidth.prototype, "net_weight", void 0);
__decorate([
    Struct.field('asset')
], AccountSelfDelegatedBandwidth.prototype, "cpu_weight", void 0);
AccountSelfDelegatedBandwidth = __decorate([
    Struct.type('account_self_delegated_bandwidth')
], AccountSelfDelegatedBandwidth);
let AccountRefundRequest = class AccountRefundRequest extends Struct {
};
__decorate([
    Struct.field('name')
], AccountRefundRequest.prototype, "owner", void 0);
__decorate([
    Struct.field('time_point')
], AccountRefundRequest.prototype, "request_time", void 0);
__decorate([
    Struct.field('asset')
], AccountRefundRequest.prototype, "net_amount", void 0);
__decorate([
    Struct.field('asset')
], AccountRefundRequest.prototype, "cpu_amount", void 0);
AccountRefundRequest = __decorate([
    Struct.type('account_refund_request')
], AccountRefundRequest);
let AccountVoterInfo = class AccountVoterInfo extends Struct {
};
__decorate([
    Struct.field('name')
], AccountVoterInfo.prototype, "owner", void 0);
__decorate([
    Struct.field('name')
], AccountVoterInfo.prototype, "proxy", void 0);
__decorate([
    Struct.field('name', { array: true })
], AccountVoterInfo.prototype, "producers", void 0);
__decorate([
    Struct.field('int64', { optional: true })
], AccountVoterInfo.prototype, "staked", void 0);
__decorate([
    Struct.field('bool')
], AccountVoterInfo.prototype, "is_proxy", void 0);
__decorate([
    Struct.field('uint32', { optional: true })
], AccountVoterInfo.prototype, "flags1", void 0);
__decorate([
    Struct.field('uint32')
], AccountVoterInfo.prototype, "reserved2", void 0);
__decorate([
    Struct.field('string')
], AccountVoterInfo.prototype, "reserved3", void 0);
AccountVoterInfo = __decorate([
    Struct.type('account_voter_info')
], AccountVoterInfo);
let AccountRexInfoMaturities = class AccountRexInfoMaturities extends Struct {
};
__decorate([
    Struct.field('time_point', { optional: true })
], AccountRexInfoMaturities.prototype, "key", void 0);
__decorate([
    Struct.field('int64', { optional: true })
], AccountRexInfoMaturities.prototype, "value", void 0);
__decorate([
    Struct.field('time_point', { optional: true })
], AccountRexInfoMaturities.prototype, "first", void 0);
__decorate([
    Struct.field('int64', { optional: true })
], AccountRexInfoMaturities.prototype, "second", void 0);
AccountRexInfoMaturities = __decorate([
    Struct.type('account_rex_info_maturities')
], AccountRexInfoMaturities);
let AccountRexInfo = class AccountRexInfo extends Struct {
};
__decorate([
    Struct.field('uint32')
], AccountRexInfo.prototype, "version", void 0);
__decorate([
    Struct.field('name')
], AccountRexInfo.prototype, "owner", void 0);
__decorate([
    Struct.field('asset')
], AccountRexInfo.prototype, "vote_stake", void 0);
__decorate([
    Struct.field('asset')
], AccountRexInfo.prototype, "rex_balance", void 0);
__decorate([
    Struct.field('int64')
], AccountRexInfo.prototype, "matured_rex", void 0);
__decorate([
    Struct.field(AccountRexInfoMaturities, { array: true })
], AccountRexInfo.prototype, "rex_maturities", void 0);
AccountRexInfo = __decorate([
    Struct.type('account_rex_info')
], AccountRexInfo);
let AccountObject = class AccountObject extends Struct {
    getPermission(permission) {
        const name = Name.from(permission);
        const match = this.permissions.find((p) => p.perm_name.equals(name));
        if (!match) {
            throw new Error(`Unknown permission ${name} on account ${this.account_name}.`);
        }
        return match;
    }
};
__decorate([
    Struct.field('name')
], AccountObject.prototype, "account_name", void 0);
__decorate([
    Struct.field('uint32')
], AccountObject.prototype, "head_block_num", void 0);
__decorate([
    Struct.field('time_point')
], AccountObject.prototype, "head_block_time", void 0);
__decorate([
    Struct.field('bool')
], AccountObject.prototype, "privileged", void 0);
__decorate([
    Struct.field('time_point')
], AccountObject.prototype, "last_code_update", void 0);
__decorate([
    Struct.field('time_point')
], AccountObject.prototype, "created", void 0);
__decorate([
    Struct.field('asset?')
], AccountObject.prototype, "core_liquid_balance", void 0);
__decorate([
    Struct.field('int64')
], AccountObject.prototype, "ram_quota", void 0);
__decorate([
    Struct.field('int64')
], AccountObject.prototype, "net_weight", void 0);
__decorate([
    Struct.field('int64')
], AccountObject.prototype, "cpu_weight", void 0);
__decorate([
    Struct.field(AccountResourceLimit)
], AccountObject.prototype, "net_limit", void 0);
__decorate([
    Struct.field(AccountResourceLimit)
], AccountObject.prototype, "cpu_limit", void 0);
__decorate([
    Struct.field('uint64')
], AccountObject.prototype, "ram_usage", void 0);
__decorate([
    Struct.field(AccountPermission, { array: true })
], AccountObject.prototype, "permissions", void 0);
__decorate([
    Struct.field(AccountTotalResources)
], AccountObject.prototype, "total_resources", void 0);
__decorate([
    Struct.field(AccountSelfDelegatedBandwidth, { optional: true })
], AccountObject.prototype, "self_delegated_bandwidth", void 0);
__decorate([
    Struct.field(AccountRefundRequest, { optional: true })
], AccountObject.prototype, "refund_request", void 0);
__decorate([
    Struct.field(AccountVoterInfo, { optional: true })
], AccountObject.prototype, "voter_info", void 0);
__decorate([
    Struct.field(AccountRexInfo, { optional: true })
], AccountObject.prototype, "rex_info", void 0);
AccountObject = __decorate([
    Struct.type('account_object')
], AccountObject);
let NewProducersEntry = class NewProducersEntry extends Struct {
};
__decorate([
    Struct.field('name')
], NewProducersEntry.prototype, "producer_name", void 0);
__decorate([
    Struct.field('public_key')
], NewProducersEntry.prototype, "block_signing_key", void 0);
NewProducersEntry = __decorate([
    Struct.type('new_producers_entry')
], NewProducersEntry);
let NewProducers = class NewProducers extends Struct {
};
__decorate([
    Struct.field('uint32')
], NewProducers.prototype, "version", void 0);
__decorate([
    Struct.field(NewProducersEntry, { array: true })
], NewProducers.prototype, "producers", void 0);
NewProducers = __decorate([
    Struct.type('new_producers')
], NewProducers);
let BlockExtension = class BlockExtension extends Struct {
};
__decorate([
    Struct.field('uint16')
], BlockExtension.prototype, "type", void 0);
__decorate([
    Struct.field('bytes')
], BlockExtension.prototype, "data", void 0);
BlockExtension = __decorate([
    Struct.type('block_extension')
], BlockExtension);
let HeaderExtension = class HeaderExtension extends Struct {
};
__decorate([
    Struct.field('uint16')
], HeaderExtension.prototype, "type", void 0);
__decorate([
    Struct.field('bytes')
], HeaderExtension.prototype, "data", void 0);
HeaderExtension = __decorate([
    Struct.type('header_extension')
], HeaderExtension);
// fc "mutable variant" returned by get_block api
class TrxVariant {
    constructor(id, extra) {
        this.id = id;
        this.extra = extra;
    }
    static from(data) {
        let id;
        let extra;
        if (typeof data === 'string') {
            id = Checksum256.from(data);
            extra = {};
        }
        else {
            id = Checksum256.from(data.id);
            extra = data;
        }
        return new this(id, extra);
    }
    get transaction() {
        if (this.extra.packed_trx) {
            return Serializer.decode({ data: this.extra.packed_trx, type: Transaction });
        }
    }
    get signatures() {
        if (this.extra.signatures) {
            return this.extra.signatures.map(Signature.from);
        }
    }
    equals(other) {
        return this.id.equals(other.id);
    }
    toJSON() {
        return this.id;
    }
}
TrxVariant.abiName = 'trx_variant';
let GetBlockResponseTransactionReceipt = class GetBlockResponseTransactionReceipt extends TransactionReceipt {
    get id() {
        return this.trx.id;
    }
};
__decorate([
    Struct.field(TrxVariant)
], GetBlockResponseTransactionReceipt.prototype, "trx", void 0);
GetBlockResponseTransactionReceipt = __decorate([
    Struct.type('get_block_response_receipt')
], GetBlockResponseTransactionReceipt);
let GetBlockResponse = class GetBlockResponse extends Struct {
};
__decorate([
    Struct.field('time_point')
], GetBlockResponse.prototype, "timestamp", void 0);
__decorate([
    Struct.field('name')
], GetBlockResponse.prototype, "producer", void 0);
__decorate([
    Struct.field('uint16')
], GetBlockResponse.prototype, "confirmed", void 0);
__decorate([
    Struct.field('checksum256')
], GetBlockResponse.prototype, "previous", void 0);
__decorate([
    Struct.field('checksum256')
], GetBlockResponse.prototype, "transaction_mroot", void 0);
__decorate([
    Struct.field('checksum256')
], GetBlockResponse.prototype, "action_mroot", void 0);
__decorate([
    Struct.field('uint32')
], GetBlockResponse.prototype, "schedule_version", void 0);
__decorate([
    Struct.field(NewProducers, { optional: true })
], GetBlockResponse.prototype, "new_producers", void 0);
__decorate([
    Struct.field('header_extension', { optional: true })
], GetBlockResponse.prototype, "header_extensions", void 0);
__decorate([
    Struct.field('any', { optional: true })
], GetBlockResponse.prototype, "new_protocol_features", void 0);
__decorate([
    Struct.field('signature')
], GetBlockResponse.prototype, "producer_signature", void 0);
__decorate([
    Struct.field(GetBlockResponseTransactionReceipt, { array: true })
], GetBlockResponse.prototype, "transactions", void 0);
__decorate([
    Struct.field('block_extension', { optional: true })
], GetBlockResponse.prototype, "block_extensions", void 0);
__decorate([
    Struct.field('checksum256')
], GetBlockResponse.prototype, "id", void 0);
__decorate([
    Struct.field('uint32')
], GetBlockResponse.prototype, "block_num", void 0);
__decorate([
    Struct.field('uint32')
], GetBlockResponse.prototype, "ref_block_prefix", void 0);
GetBlockResponse = __decorate([
    Struct.type('get_block_response')
], GetBlockResponse);
let ActiveScheduleProducerAuthority = class ActiveScheduleProducerAuthority extends Struct {
};
__decorate([
    Struct.field('name')
], ActiveScheduleProducerAuthority.prototype, "producer_name", void 0);
__decorate([
    Struct.field('any')
], ActiveScheduleProducerAuthority.prototype, "authority", void 0);
ActiveScheduleProducerAuthority = __decorate([
    Struct.type('active_schedule_producer_authority')
], ActiveScheduleProducerAuthority);
let ActiveScheduleProducer = class ActiveScheduleProducer extends Struct {
};
__decorate([
    Struct.field('name')
], ActiveScheduleProducer.prototype, "producer_name", void 0);
__decorate([
    Struct.field(ActiveScheduleProducerAuthority)
], ActiveScheduleProducer.prototype, "authority", void 0);
ActiveScheduleProducer = __decorate([
    Struct.type('active_schedule_producer')
], ActiveScheduleProducer);
let ActiveSchedule = class ActiveSchedule extends Struct {
};
__decorate([
    Struct.field('uint32')
], ActiveSchedule.prototype, "version", void 0);
__decorate([
    Struct.field(ActiveScheduleProducer, { array: true })
], ActiveSchedule.prototype, "producers", void 0);
ActiveSchedule = __decorate([
    Struct.type('active_schedule')
], ActiveSchedule);
let BlockStateHeader = class BlockStateHeader extends Struct {
};
__decorate([
    Struct.field('time_point')
], BlockStateHeader.prototype, "timestamp", void 0);
__decorate([
    Struct.field('name')
], BlockStateHeader.prototype, "producer", void 0);
__decorate([
    Struct.field('uint16')
], BlockStateHeader.prototype, "confirmed", void 0);
__decorate([
    Struct.field('checksum256')
], BlockStateHeader.prototype, "previous", void 0);
__decorate([
    Struct.field('checksum256')
], BlockStateHeader.prototype, "transaction_mroot", void 0);
__decorate([
    Struct.field('checksum256')
], BlockStateHeader.prototype, "action_mroot", void 0);
__decorate([
    Struct.field('uint32')
], BlockStateHeader.prototype, "schedule_version", void 0);
__decorate([
    Struct.field(HeaderExtension, { array: true, optional: true })
], BlockStateHeader.prototype, "header_extensions", void 0);
__decorate([
    Struct.field('signature')
], BlockStateHeader.prototype, "producer_signature", void 0);
BlockStateHeader = __decorate([
    Struct.type('block_state_header')
], BlockStateHeader);
let GetBlockHeaderStateResponse = class GetBlockHeaderStateResponse extends Struct {
};
__decorate([
    Struct.field('uint32')
], GetBlockHeaderStateResponse.prototype, "block_num", void 0);
__decorate([
    Struct.field('uint32')
], GetBlockHeaderStateResponse.prototype, "dpos_proposed_irreversible_blocknum", void 0);
__decorate([
    Struct.field('uint32')
], GetBlockHeaderStateResponse.prototype, "dpos_irreversible_blocknum", void 0);
__decorate([
    Struct.field('checksum256')
], GetBlockHeaderStateResponse.prototype, "id", void 0);
__decorate([
    Struct.field(BlockStateHeader)
], GetBlockHeaderStateResponse.prototype, "header", void 0);
__decorate([
    Struct.field('any')
], GetBlockHeaderStateResponse.prototype, "active_schedule", void 0);
__decorate([
    Struct.field('any')
], GetBlockHeaderStateResponse.prototype, "blockroot_merkle", void 0);
__decorate([
    Struct.field('any')
], GetBlockHeaderStateResponse.prototype, "producer_to_last_produced", void 0);
__decorate([
    Struct.field('any')
], GetBlockHeaderStateResponse.prototype, "producer_to_last_implied_irb", void 0);
__decorate([
    Struct.field('any')
], GetBlockHeaderStateResponse.prototype, "valid_block_signing_authority", void 0);
__decorate([
    Struct.field('any')
], GetBlockHeaderStateResponse.prototype, "confirm_count", void 0);
__decorate([
    Struct.field('any')
], GetBlockHeaderStateResponse.prototype, "pending_schedule", void 0);
__decorate([
    Struct.field('any')
], GetBlockHeaderStateResponse.prototype, "activated_protocol_features", void 0);
__decorate([
    Struct.field('any')
], GetBlockHeaderStateResponse.prototype, "additional_signatures", void 0);
GetBlockHeaderStateResponse = __decorate([
    Struct.type('get_block_header_state_response')
], GetBlockHeaderStateResponse);
let GetInfoResponse = class GetInfoResponse extends Struct {
    getTransactionHeader(secondsAhead = 120) {
        const expiration = TimePointSec.fromMilliseconds(this.head_block_time.toMilliseconds() + secondsAhead * 1000);
        const id = this.last_irreversible_block_id;
        const prefixArray = id.array.subarray(8, 12);
        const prefix = new Uint32Array(prefixArray.buffer, prefixArray.byteOffset, 1)[0];
        return TransactionHeader.from({
            expiration,
            ref_block_num: Number(this.last_irreversible_block_num) & 0xffff,
            ref_block_prefix: prefix,
        });
    }
};
__decorate([
    Struct.field('string')
], GetInfoResponse.prototype, "server_version", void 0);
__decorate([
    Struct.field('checksum256')
], GetInfoResponse.prototype, "chain_id", void 0);
__decorate([
    Struct.field('uint32')
], GetInfoResponse.prototype, "head_block_num", void 0);
__decorate([
    Struct.field('uint32')
], GetInfoResponse.prototype, "last_irreversible_block_num", void 0);
__decorate([
    Struct.field('checksum256')
], GetInfoResponse.prototype, "last_irreversible_block_id", void 0);
__decorate([
    Struct.field('checksum256')
], GetInfoResponse.prototype, "head_block_id", void 0);
__decorate([
    Struct.field('time_point')
], GetInfoResponse.prototype, "head_block_time", void 0);
__decorate([
    Struct.field('name')
], GetInfoResponse.prototype, "head_block_producer", void 0);
__decorate([
    Struct.field('uint64')
], GetInfoResponse.prototype, "virtual_block_cpu_limit", void 0);
__decorate([
    Struct.field('uint64')
], GetInfoResponse.prototype, "virtual_block_net_limit", void 0);
__decorate([
    Struct.field('uint64')
], GetInfoResponse.prototype, "block_cpu_limit", void 0);
__decorate([
    Struct.field('uint64')
], GetInfoResponse.prototype, "block_net_limit", void 0);
__decorate([
    Struct.field('string?')
], GetInfoResponse.prototype, "server_version_string", void 0);
__decorate([
    Struct.field('uint32?')
], GetInfoResponse.prototype, "fork_db_head_block_num", void 0);
__decorate([
    Struct.field('checksum256?')
], GetInfoResponse.prototype, "fork_db_head_block_id", void 0);
GetInfoResponse = __decorate([
    Struct.type('get_info_response')
], GetInfoResponse);
let GetTableByScopeResponseRow = class GetTableByScopeResponseRow extends Struct {
};
__decorate([
    Struct.field('name')
], GetTableByScopeResponseRow.prototype, "code", void 0);
__decorate([
    Struct.field('name')
], GetTableByScopeResponseRow.prototype, "scope", void 0);
__decorate([
    Struct.field('name')
], GetTableByScopeResponseRow.prototype, "table", void 0);
__decorate([
    Struct.field('name')
], GetTableByScopeResponseRow.prototype, "payer", void 0);
__decorate([
    Struct.field('uint32')
], GetTableByScopeResponseRow.prototype, "count", void 0);
GetTableByScopeResponseRow = __decorate([
    Struct.type('get_table_by_scope_response_row')
], GetTableByScopeResponseRow);
let GetTableByScopeResponse = class GetTableByScopeResponse extends Struct {
};
__decorate([
    Struct.field(GetTableByScopeResponseRow, { array: true })
], GetTableByScopeResponse.prototype, "rows", void 0);
__decorate([
    Struct.field('string')
], GetTableByScopeResponse.prototype, "more", void 0);
GetTableByScopeResponse = __decorate([
    Struct.type('get_table_by_scope_response')
], GetTableByScopeResponse);
let OrderedActionsResult = class OrderedActionsResult extends Struct {
};
__decorate([
    Struct.field(UInt64)
], OrderedActionsResult.prototype, "global_action_seq", void 0);
__decorate([
    Struct.field(Int64)
], OrderedActionsResult.prototype, "account_action_seq", void 0);
__decorate([
    Struct.field(UInt32)
], OrderedActionsResult.prototype, "block_num", void 0);
__decorate([
    Struct.field(BlockTimestamp)
], OrderedActionsResult.prototype, "block_time", void 0);
__decorate([
    Struct.field('any')
], OrderedActionsResult.prototype, "action_trace", void 0);
__decorate([
    Struct.field('boolean?')
], OrderedActionsResult.prototype, "irrevirsible", void 0);
OrderedActionsResult = __decorate([
    Struct.type('ordered_action_result')
], OrderedActionsResult);
let GetActionsResponse = class GetActionsResponse extends Struct {
};
__decorate([
    Struct.field(OrderedActionsResult, { array: true })
], GetActionsResponse.prototype, "actions", void 0);
__decorate([
    Struct.field(Int32)
], GetActionsResponse.prototype, "last_irreversible_block", void 0);
__decorate([
    Struct.field(Int32)
], GetActionsResponse.prototype, "head_block_num", void 0);
__decorate([
    Struct.field('boolean?')
], GetActionsResponse.prototype, "time_limit_exceeded_error", void 0);
GetActionsResponse = __decorate([
    Struct.type('get_actions_response')
], GetActionsResponse);
let TransactionTrace = class TransactionTrace extends Struct {
};
TransactionTrace = __decorate([
    Struct.type('transaction_trace')
], TransactionTrace);
let Trx = class Trx extends Struct {
};
__decorate([
    Struct.field('any')
], Trx.prototype, "actions", void 0);
__decorate([
    Struct.field('any')
], Trx.prototype, "context_free_actions", void 0);
__decorate([
    Struct.field('any')
], Trx.prototype, "context_free_data", void 0);
__decorate([
    Struct.field('number')
], Trx.prototype, "delay_sec", void 0);
__decorate([
    Struct.field('string')
], Trx.prototype, "expiration", void 0);
__decorate([
    Struct.field('number')
], Trx.prototype, "max_cpu_usage_ms", void 0);
__decorate([
    Struct.field('number')
], Trx.prototype, "max_net_usage_words", void 0);
__decorate([
    Struct.field('number')
], Trx.prototype, "ref_block_num", void 0);
__decorate([
    Struct.field('number')
], Trx.prototype, "ref_block_prefix", void 0);
__decorate([
    Struct.field('string', { array: true })
], Trx.prototype, "signatures", void 0);
Trx = __decorate([
    Struct.type('trx')
], Trx);
let TransactionInfo = class TransactionInfo extends Struct {
};
__decorate([
    Struct.field(TransactionReceipt)
], TransactionInfo.prototype, "receipt", void 0);
__decorate([
    Struct.field('trx')
], TransactionInfo.prototype, "trx", void 0);
TransactionInfo = __decorate([
    Struct.type('transaction_info')
], TransactionInfo);
let GetTransactionResponse = class GetTransactionResponse extends Struct {
};
__decorate([
    Struct.field(Checksum256)
], GetTransactionResponse.prototype, "id", void 0);
__decorate([
    Struct.field(UInt32)
], GetTransactionResponse.prototype, "block_num", void 0);
__decorate([
    Struct.field(BlockTimestamp)
], GetTransactionResponse.prototype, "block_time", void 0);
__decorate([
    Struct.field(UInt32)
], GetTransactionResponse.prototype, "last_irreversible_block", void 0);
__decorate([
    Struct.field('any?')
], GetTransactionResponse.prototype, "traces", void 0);
__decorate([
    Struct.field('any')
], GetTransactionResponse.prototype, "trx", void 0);
GetTransactionResponse = __decorate([
    Struct.type('get_transaction_response')
], GetTransactionResponse);
let GetKeyAccountsResponse = class GetKeyAccountsResponse extends Struct {
};
__decorate([
    Struct.field('name', { array: true })
], GetKeyAccountsResponse.prototype, "account_names", void 0);
GetKeyAccountsResponse = __decorate([
    Struct.type('get_key_accounts_response')
], GetKeyAccountsResponse);
let GetControlledAccountsResponse = class GetControlledAccountsResponse extends Struct {
};
__decorate([
    Struct.field('name', { array: true })
], GetControlledAccountsResponse.prototype, "controlled_accounts", void 0);
GetControlledAccountsResponse = __decorate([
    Struct.type('get_controlled_accounts_response')
], GetControlledAccountsResponse);

var types$1 = /*#__PURE__*/Object.freeze({
    __proto__: null,
    get AccountPermission () { return AccountPermission; },
    get AccountResourceLimit () { return AccountResourceLimit; },
    get AccountTotalResources () { return AccountTotalResources; },
    get AccountSelfDelegatedBandwidth () { return AccountSelfDelegatedBandwidth; },
    get AccountRefundRequest () { return AccountRefundRequest; },
    get AccountVoterInfo () { return AccountVoterInfo; },
    get AccountRexInfoMaturities () { return AccountRexInfoMaturities; },
    get AccountRexInfo () { return AccountRexInfo; },
    get AccountObject () { return AccountObject; },
    get NewProducersEntry () { return NewProducersEntry; },
    get NewProducers () { return NewProducers; },
    get BlockExtension () { return BlockExtension; },
    get HeaderExtension () { return HeaderExtension; },
    TrxVariant: TrxVariant,
    get GetBlockResponseTransactionReceipt () { return GetBlockResponseTransactionReceipt; },
    get GetBlockResponse () { return GetBlockResponse; },
    get ActiveScheduleProducerAuthority () { return ActiveScheduleProducerAuthority; },
    get ActiveScheduleProducer () { return ActiveScheduleProducer; },
    get ActiveSchedule () { return ActiveSchedule; },
    get BlockStateHeader () { return BlockStateHeader; },
    get GetBlockHeaderStateResponse () { return GetBlockHeaderStateResponse; },
    get GetInfoResponse () { return GetInfoResponse; },
    get GetTableByScopeResponseRow () { return GetTableByScopeResponseRow; },
    get GetTableByScopeResponse () { return GetTableByScopeResponse; },
    get OrderedActionsResult () { return OrderedActionsResult; },
    get GetActionsResponse () { return GetActionsResponse; },
    get TransactionTrace () { return TransactionTrace; },
    get Trx () { return Trx; },
    get TransactionInfo () { return TransactionInfo; },
    get GetTransactionResponse () { return GetTransactionResponse; },
    get GetKeyAccountsResponse () { return GetKeyAccountsResponse; },
    get GetControlledAccountsResponse () { return GetControlledAccountsResponse; }
});

class ChainAPI {
    constructor(client) {
        this.client = client;
    }
    async get_abi(accountName) {
        return this.client.call({
            path: '/v1/chain/get_abi',
            params: { account_name: Name.from(accountName) },
        });
    }
    async get_account(accountName) {
        return this.client.call({
            path: '/v1/chain/get_account',
            params: { account_name: Name.from(accountName) },
            responseType: AccountObject,
        });
    }
    async get_block(block_num_or_id) {
        return this.client.call({
            path: '/v1/chain/get_block',
            params: { block_num_or_id },
            responseType: GetBlockResponse,
        });
    }
    async get_block_header_state(block_num_or_id) {
        return this.client.call({
            path: '/v1/chain/get_block_header_state',
            params: { block_num_or_id },
            responseType: GetBlockHeaderStateResponse,
        });
    }
    async get_currency_balance(contract, accountName, symbol) {
        const params = {
            account: Name.from(accountName),
            code: Name.from(contract),
        };
        if (symbol) {
            params.symbol = symbol;
        }
        return this.client.call({
            path: '/v1/chain/get_currency_balance',
            params,
            responseType: 'asset[]',
        });
    }
    async get_info() {
        return this.client.call({
            path: '/v1/chain/get_info',
            responseType: GetInfoResponse,
        });
    }
    async push_transaction(tx) {
        if (!isInstanceOf(tx, PackedTransaction)) {
            tx = PackedTransaction.fromSigned(SignedTransaction.from(tx));
        }
        return this.client.call({
            path: '/v1/chain/push_transaction',
            params: tx,
        });
    }
    async get_table_rows(params) {
        const type = params.type;
        let key_type = params.key_type;
        const someBound = params.lower_bound || params.upper_bound;
        if (!key_type && someBound) {
            // determine key type from bounds type
            if (isInstanceOf(someBound, UInt64)) {
                key_type = 'i64';
            }
            else if (isInstanceOf(someBound, UInt128)) {
                key_type = 'i128';
            }
            else if (isInstanceOf(someBound, Checksum256)) {
                key_type = 'sha256';
            }
            else if (isInstanceOf(someBound, Checksum160)) {
                key_type = 'ripemd160';
            }
        }
        if (!key_type) {
            key_type = 'name';
        }
        let json = params.json;
        if (json === undefined) {
            // if we know the row type don't ask the node to perform abi decoding
            json = type === undefined;
        }
        let upper_bound = params.upper_bound;
        if (upper_bound && typeof upper_bound !== 'string') {
            upper_bound = String(upper_bound);
        }
        let lower_bound = params.lower_bound;
        if (lower_bound && typeof lower_bound !== 'string') {
            lower_bound = String(lower_bound);
        }
        let scope = params.scope;
        if (typeof scope === 'undefined') {
            scope = String(Name.from(params.code));
        }
        else if (typeof scope !== 'string') {
            scope = String(scope);
        }
        // eslint-disable-next-line prefer-const
        let { rows, more, next_key } = await this.client.call({
            path: '/v1/chain/get_table_rows',
            params: {
                ...params,
                code: Name.from(params.code),
                table: Name.from(params.table),
                limit: params.limit !== undefined ? UInt32.from(params.limit) : undefined,
                scope,
                key_type,
                json,
                upper_bound,
                lower_bound,
            },
        });
        let ram_payers;
        if (params.show_payer) {
            ram_payers = [];
            rows = rows.map(({ data, payer }) => {
                ram_payers.push(Name.from(payer));
                return data;
            });
        }
        if (type) {
            if (json) {
                rows = rows.map((value) => {
                    if (typeof value === 'string' && Bytes.isBytes(value)) {
                        // this handles the case where nodeos bails on abi decoding and just returns a hex string
                        return Serializer.decode({ data: Bytes.from(value), type });
                    }
                    else {
                        return Serializer.decode({ object: value, type });
                    }
                });
            }
            else {
                rows = rows
                    .map((hex) => Bytes.from(hex))
                    .map((data) => Serializer.decode({ data, type }));
            }
        }
        if (next_key && next_key.length > 0) {
            let indexType;
            // set index type so we can decode next_key in the response if present
            switch (key_type) {
                case 'i64':
                    indexType = UInt64;
                    break;
                case 'i128':
                    indexType = UInt128;
                    break;
                case 'name':
                    indexType = Name;
                    break;
                case 'float64':
                    indexType = Float64;
                    break;
                case 'float128':
                    indexType = Float128;
                    break;
                case 'sha256':
                    indexType = Checksum256;
                    break;
                case 'ripemd160':
                    indexType = Checksum160;
                    break;
                default:
                    throw new Error(`Unsupported key type: ${key_type}`);
            }
            if (indexType === Name) {
                // names are sent back as an uint64 string instead of a name string..
                next_key = Name.from(Serializer.decode({ object: next_key, type: UInt64 }));
            }
            else {
                next_key = Serializer.decode({ object: next_key, type: indexType });
            }
        }
        else {
            next_key = undefined;
        }
        return { rows, more, next_key, ram_payers };
    }
    async get_table_by_scope(params) {
        return this.client.call({
            path: '/v1/chain/get_table_by_scope',
            params,
            responseType: GetTableByScopeResponse,
        });
    }
}

class HistoryAPI {
    constructor(client) {
        this.client = client;
    }
    async get_actions(accountName, pos, offset) {
        return this.client.call({
            path: '/v1/history/get_actions',
            params: {
                account_name: Name.from(accountName),
                pos: Int32.from(pos),
                offset: Int32.from(offset),
            },
            responseType: GetActionsResponse,
        });
    }
    async get_transaction(id, options = {}) {
        return this.client.call({
            path: '/v1/history/get_transaction',
            params: {
                id: Checksum256.from(id),
                block_num_hint: options.blockNumHint && UInt32.from(options.blockNumHint),
                traces: options.excludeTraces === true ? false : undefined,
            },
            responseType: GetTransactionResponse,
        });
    }
    async get_key_accounts(publicKey) {
        return this.client.call({
            path: '/v1/history/get_key_accounts',
            params: { public_key: PublicKey.from(publicKey) },
            responseType: GetKeyAccountsResponse,
        });
    }
    async get_controlled_accounts(controllingAccount) {
        return this.client.call({
            path: '/v1/history/get_controlled_accounts',
            params: { controlling_account: Name.from(controllingAccount) },
            responseType: GetControlledAccountsResponse,
        });
    }
}

class APIError extends Error {
    constructor(path, response) {
        let message;
        if (response.json && response.json.error) {
            message = `${APIError.formatError(response.json.error)} at ${path}`;
        }
        else {
            message = `HTTP ${response.status} at ${path}`;
        }
        super(message);
        this.path = path;
        this.response = response;
    }
    static formatError(error) {
        if (error.what === 'unspecified' &&
            error.details[0].file &&
            error.details[0].file === 'http_plugin.cpp' &&
            error.details[0].message.slice(0, 11) === 'unknown key') {
            // fix cryptic error messages from nodeos for missing accounts
            return 'Account not found';
        }
        else if (error.what === 'unspecified' && error.details && error.details.length > 0) {
            return error.details[0].message;
        }
        else if (error.what && error.what.length > 0) {
            return error.what;
        }
        else {
            return 'Unknown API error';
        }
    }
    /** The nodeos error object. */
    get error() {
        const { json } = this.response;
        return (json ? json.error : undefined);
    }
    /** The nodeos error name, e.g. `tx_net_usage_exceeded` */
    get name() {
        const { error } = this;
        return error ? error.name : 'unspecified';
    }
    /** The nodeos error code, e.g. `3080002`. */
    get code() {
        const { error } = this;
        return error ? error.code : 0;
    }
    /** List of exceptions, if any. */
    get details() {
        const { error } = this;
        return error ? error.details : [];
    }
}
APIError.__className = 'APIError';
class APIClient {
    constructor(options) {
        this.v1 = {
            chain: new ChainAPI(this),
            history: new HistoryAPI(this),
        };
        if (options.provider) {
            this.provider = options.provider;
        }
        else if (options.url) {
            this.provider = new FetchProvider(options.url, options);
        }
        else {
            throw new Error('Missing url or provider');
        }
    }
    async call(args) {
        const response = await this.provider.call(args.path, args.params);
        const { json } = response;
        if (Math.floor(response.status / 100) !== 2 || (json && typeof json.error === 'object')) {
            throw new APIError(args.path, response);
        }
        if (args.responseType) {
            return abiDecode({ type: args.responseType, object: response.json });
        }
        return response.json || response.text;
    }
}
APIClient.__className = 'APIClient';

var types = /*#__PURE__*/Object.freeze({
    __proto__: null,
    v1: types$1
});

export { ABI, ABIDecoder, ABIEncoder, types as API, APIClient, APIError, Action, Asset, Authority, Base58, BlockTimestamp, Bytes, Checksum160, Checksum256, Checksum512, ExtendedAsset, FetchProvider, Float128, Float32, Float64, Int, Int128, Int16, Int32, Int64, Int8, KeyType, KeyWeight, Name, PackedTransaction, PermissionLevel, PermissionLevelWeight, PrivateKey, PublicKey, Serializer, Signature, SignedTransaction, Struct, TimePoint, TimePointSec, Transaction, TransactionExtension, TransactionHeader, TransactionReceipt, TypeAlias, UInt128, UInt16, UInt32, UInt64, UInt8, VarInt, VarUInt, Variant, WaitWeight, Weight, isInstanceOf };
//# sourceMappingURL=eosio-core.m.js.map
