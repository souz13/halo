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
import BN from 'bn.js';

interface BuiltinTypes {
    string: string;
    'string?'?: string;
    'string[]': string[];
    'string[]?'?: string[];
    bool: boolean;
    'bool?'?: boolean;
    'bool[]': boolean[];
    'bool[]?'?: boolean[];
    asset: Asset;
    'asset?'?: Asset;
    'asset[]': Asset[];
    'asset[]?'?: Asset[];
    extended_asset: ExtendedAsset;
    'extended_asset?'?: ExtendedAsset;
    'extended_asset[]': ExtendedAsset[];
    'extended_asset[]?'?: ExtendedAsset[];
    bytes: Bytes;
    'bytes?'?: Bytes;
    'bytes[]': Bytes[];
    'bytes[]?'?: Bytes[];
    checksum160: Checksum160;
    'checksum160?'?: Checksum160;
    'checksum160[]': Checksum160[];
    'checksum160[]?'?: Checksum160[];
    checksum256: Checksum256;
    'checksum256?'?: Checksum256;
    'checksum256[]': Checksum256[];
    'checksum256[]?'?: Checksum256[];
    checksum512: Checksum512;
    'checksum512?'?: Checksum512;
    'checksum512[]': Checksum512[];
    'checksum512[]?'?: Checksum512[];
    name: Name;
    'name?'?: Name;
    'name[]': Name[];
    'name[]?'?: Name[];
    publickey: PublicKey;
    'publickey?'?: PublicKey;
    'publickey[]': PublicKey[];
    'publickey[]?'?: PublicKey[];
    signature: Signature;
    'signature?'?: Signature;
    'signature[]': Signature[];
    'signature[]?'?: Signature[];
    symbol: Asset.Symbol;
    'symbol?'?: Asset.Symbol;
    'symbol[]': Asset.Symbol[];
    'symbol[]?'?: Asset.Symbol[];
    symbol_code: Asset.SymbolCode;
    'symbol_code?'?: Asset.SymbolCode;
    'symbol_code[]': Asset.SymbolCode[];
    'symbol_code[]?'?: Asset.SymbolCode[];
    time_point: TimePoint;
    'time_point?'?: TimePoint;
    'time_point[]': TimePoint[];
    'time_point[]?'?: TimePoint[];
    time_point_sec: TimePointSec;
    'time_point_sec?'?: TimePointSec;
    'time_point_sec[]': TimePointSec[];
    'time_point_sec[]?'?: TimePointSec[];
    block_timestamp_type: BlockTimestamp;
    'block_timestamp_type?'?: BlockTimestamp;
    'block_timestamp_type[]': BlockTimestamp[];
    'block_timestamp_type[]?'?: BlockTimestamp[];
    int8: Int8;
    'int8?'?: Int8;
    'int8[]': Int8[];
    'int8[]?'?: Int8[];
    int16: Int16;
    'int16?'?: Int16;
    'int16[]': Int16[];
    'int16[]?'?: Int16[];
    int32: Int32;
    'int32?'?: Int32;
    'int32[]': Int32[];
    'int32[]?'?: Int32[];
    int64: Int64;
    'int64?'?: Int64;
    'int64[]': Int64[];
    'int64[]?'?: Int64[];
    int128: Int128;
    'int128?'?: Int128;
    'int128[]': Int128[];
    'int128[]?'?: Int128[];
    uint8: UInt8;
    'uint8?'?: UInt8;
    'uint8[]': UInt8[];
    'uint8[]?'?: UInt8[];
    uint16: UInt16;
    'uint16?'?: UInt16;
    'uint16[]': UInt16[];
    'uint16[]?'?: UInt16[];
    uint32: UInt32;
    'uint32?'?: UInt32;
    'uint32[]': UInt32[];
    'uint32[]?'?: UInt32[];
    uint64: UInt64;
    'uint64?'?: UInt64;
    'uint64[]': UInt64[];
    'uint64[]?'?: UInt64[];
    uint128: UInt128;
    'uint128?'?: UInt128;
    'uint128[]': UInt128[];
    'uint128[]?'?: UInt128[];
    varint: VarInt;
    'varint?'?: VarInt;
    'varint[]': VarInt[];
    'varint[]?'?: VarInt[];
    varuint: VarUInt;
    'varuint?'?: VarUInt;
    'varuint[]': VarUInt[];
    'varuint[]?'?: VarUInt[];
    float32: Float32;
    'float32?'?: Float32;
    'float32[]': Float32[];
    'float32[]?'?: Float32[];
    float64: Float64;
    'float64?'?: Float64;
    'float64[]': Float64[];
    'float64[]?'?: Float64[];
    float128: Float128;
    'float128?'?: Float128;
    'float128[]': Float128[];
    'float128[]?'?: Float128[];
}

/**
 * EOSIO ABI Decoder
 */

interface DecodeArgsBase {
    abi?: ABIDef;
    data?: BytesType | ABIDecoder;
    json?: string;
    object?: any;
    customTypes?: ABISerializableConstructor[];
    /** Optional encoder metadata.  */
    metadata?: Record<string, any>;
}
interface TypedDecodeArgs<T extends ABISerializableType> extends DecodeArgsBase {
    type: T;
}
interface BuiltinDecodeArgs<T extends keyof BuiltinTypes> extends DecodeArgsBase {
    type: T;
}
interface UntypedDecodeArgs extends DecodeArgsBase {
    type: ABISerializableType;
}
declare function abiDecode<T extends keyof BuiltinTypes>(args: BuiltinDecodeArgs<T>): BuiltinTypes[T];
declare function abiDecode<T extends ABISerializableConstructor>(args: TypedDecodeArgs<T>): InstanceType<T>;
declare function abiDecode(args: UntypedDecodeArgs): ABISerializable;
declare class ABIDecoder {
    private array;
    static __className: string;
    private pos;
    private data;
    private textDecoder;
    /** User declared metadata, can be used to pass info to instances when decoding.  */
    metadata: Record<string, any>;
    constructor(array: Uint8Array);
    canRead(bytes?: number): boolean;
    private ensure;
    setPosition(pos: number): void;
    getPosition(): number;
    advance(bytes: number): void;
    /** Read one byte. */
    readByte(): number;
    /** Read floating point as JavaScript number, 32 or 64 bits. */
    readFloat(byteWidth: number): number;
    readVaruint32(): number;
    readVarint32(): number;
    readArray(length: number): Uint8Array;
    readString(): string;
}

/**
 * EOSIO ABI Encoder
 */

interface EncodeArgsBase {
    /**
     * ABI definition to use when encoding.
     */
    abi?: ABIDef;
    /**
     * Additional types to use when encoding, can be used to pass type constructors
     * that should be used when encountering a custom type.
     */
    customTypes?: ABISerializableConstructor[];
    /**
     * Can be passed to use a custom ABIEncoder instance.
     */
    encoder?: ABIEncoder;
    /**
     * Optional metadata to pass to the encoder.
     */
    metadata?: Record<string, any>;
}
interface EncodeArgsUntyped extends EncodeArgsBase {
    /**
     * Object to encode, either a object conforming to `ABISerializable`
     * or a JavaScript object, when the latter is used an the `type`
     * argument must also be set.
     */
    object: any;
    /**
     * Type to use when encoding the given object, either a type constructor
     * or a string name of a builtin type or a custom type in the given `abi`.
     */
    type: ABISerializableType;
}
interface EncodeArgsSerializable extends EncodeArgsBase {
    /**
     * Object conforming to `ABISerializable` to be encoded.
     */
    object: ABISerializable;
    /**
     * Optional type-override for given serializable object.
     */
    type?: ABISerializableType;
}
declare type EncodeArgs = EncodeArgsSerializable | EncodeArgsUntyped;
declare function abiEncode(args: EncodeArgs): Bytes;
declare class ABIEncoder {
    private pageSize;
    static __className: string;
    private pos;
    private data;
    private array;
    private textEncoder;
    /** User declared metadata, can be used to pass info to instances when encoding.  */
    metadata: Record<string, any>;
    constructor(pageSize?: number);
    private ensure;
    /** Write a single byte. */
    writeByte(byte: number): void;
    /** Write an array of bytes. */
    writeArray(bytes: ArrayLike<number>): void;
    writeFloat(value: number, byteWidth: number): void;
    writeVaruint32(v: number): void;
    writeVarint32(v: number): void;
    writeString(v: string): void;
    getData(): Uint8Array;
    getBytes(): Bytes;
}

/** A self-describing object that can be ABI encoded and decoded. */
declare type ABISerializable = ABISerializableObject | string | boolean | ABISerializable[] | {
    [key: string]: ABISerializable;
};
/** Type describing an ABI type, either a string (e.g. `uint32[]`) or a ABI type class. */
declare type ABISerializableType = string | ABISerializableConstructor | ABITypeDescriptor;
/** Interface that should be implemented by ABI serializable objects. */
interface ABISerializableObject {
    /** Called when encoding to binary abi format. */
    toABI?(encoder: ABIEncoder): void;
    /** Called when encoding to json abi format. */
    toJSON(): any;
    /** Return true if the object equals the other object passed. */
    equals(other: any): boolean;
}
interface ABITypeDescriptor {
    type: ABISerializableConstructor | string;
    optional?: boolean;
    array?: boolean;
    extension?: boolean;
}
interface ABIField extends ABITypeDescriptor {
    name: string;
    default?: any;
}
interface ABISerializableConstructor {
    /** Name of the type, e.g. `asset`. */
    abiName: string;
    /** For structs, the fields that this type contains. */
    abiFields?: ABIField[];
    /** For structs, the base class this type extends. */
    abiBase?: ABISerializableConstructor;
    /** For variants, the different types this type can represent. */
    abiVariant?: ABITypeDescriptor[];
    /** Alias to another type. */
    abiAlias?: ABITypeDescriptor;
    /**
     * Create new instance from JavaScript object.
     * Should also accept an instance of itself and return that unchanged.
     */
    from(value: any): ABISerializable;
    /**
     * Create instance from binary ABI data.
     * @param decoder Decoder instance to read from.
     */
    fromABI?(decoder: ABIDecoder): ABISerializable;
    /**
     * Static ABI encoding can be used to encode non-class types.
     * Will be used in favor of instance.toABI if both exists.
     * @param value The value to encode.
     * @param encoder The encoder to write the value to.
     */
    toABI?(value: any, encoder: ABIEncoder): void;
    /**
     * Create a new instance, don't use this other than from a custom `from` factory method.
     * @internal
     */
    new (...args: any[]): ABISerializableObject;
}

declare type BytesType = Bytes | ArrayBufferView | ArrayBuffer | ArrayLike<number> | string;
declare type AnyBytes = BytesType | {
    array: Uint8Array;
};
declare type BytesEncoding = 'hex' | 'utf8';
declare class Bytes implements ABISerializableObject {
    static abiName: string;
    /**
     * Create a new Bytes instance.
     * @note Make sure to take a [[copy]] before mutating the bytes as the underlying source is not copied here.
     */
    static from(value: AnyBytes, encoding?: BytesEncoding): Bytes;
    static fromString(value: string, encoding?: BytesEncoding): Bytes;
    static fromABI(decoder: ABIDecoder): Bytes;
    static equal(a: BytesType, b: BytesType): boolean;
    static random(length: number): Bytes;
    /** Return true if given value is a valid `BytesType`. */
    static isBytes(value: any): value is BytesType;
    array: Uint8Array;
    constructor(array?: Uint8Array);
    get hexString(): string;
    get utf8String(): string;
    /** Mutating. Append bytes to this instance. */
    append(other: AnyBytes): void;
    /** Non-mutating, returns a copy of this instance with appended bytes. */
    appending(other: AnyBytes): Bytes;
    droppingFirst(n?: number): Bytes;
    copy(): Bytes;
    equals(other: AnyBytes): boolean;
    toString(encoding?: BytesEncoding): string;
    toABI(encoder: ABIEncoder): void;
    toJSON(): string;
}

declare type ChecksumType = Checksum | BytesType;
declare class Checksum implements ABISerializableObject {
    static abiName: string;
    static byteSize: number;
    static from<T extends typeof Checksum>(this: T, value: ChecksumType): InstanceType<T>;
    static from(value: ChecksumType): unknown;
    static fromABI<T extends typeof Checksum>(this: T, decoder: ABIDecoder): InstanceType<T>;
    static fromABI(decoder: ABIDecoder): unknown;
    readonly array: Uint8Array;
    constructor(array: Uint8Array);
    equals(other: Checksum160Type | Checksum256Type | Checksum512Type): boolean;
    get hexString(): string;
    toABI(encoder: ABIEncoder): void;
    toString(): string;
    toJSON(): string;
}
declare type Checksum256Type = Checksum256 | BytesType;
declare class Checksum256 extends Checksum {
    static abiName: string;
    static byteSize: number;
    static from(value: Checksum256Type): Checksum256;
    static hash(data: BytesType): Checksum256;
}
declare type Checksum512Type = Checksum512 | BytesType;
declare class Checksum512 extends Checksum {
    static abiName: string;
    static byteSize: number;
    static from(value: Checksum512Type): Checksum512;
    static hash(data: BytesType): Checksum512;
}
declare type Checksum160Type = Checksum160 | BytesType;
declare class Checksum160 extends Checksum {
    static abiName: string;
    static byteSize: number;
    static from(value: Checksum160Type): Checksum160;
    static hash(data: BytesType): Checksum160;
}

/** Supported EOSIO curve types. */
declare enum KeyType {
    K1 = "K1",
    R1 = "R1",
    WA = "WA"
}
declare namespace KeyType {
    function indexFor(value: KeyType): 0 | 2 | 1;
    function from(value: number | string): KeyType;
}

declare type IntType = Int | number | string | BN;
/**
 * How to handle integer overflow.
 * - `throw`: Throws an error if value overflows (or underflows).
 * - `truncate`: Truncates or extends bit-pattern with sign extension (C++11 behavior).
 * - `clamp`: Clamps the value within the supported range.
 */
declare type OverflowBehavior = 'throw' | 'truncate' | 'clamp';
/**
 * How to handle remainder when dividing integers.
 * - `floor`: Round down to nearest integer.
 * - `round`: Round to nearest integer.
 * - `ceil`: Round up to nearest integer.
 */
declare type DivisionBehavior = 'floor' | 'round' | 'ceil';
/**
 * Binary integer with the underlying value represented by a BN.js instance.
 * Follows C++11 standard for arithmetic operators and conversions.
 * @note This type is optimized for correctness not speed, if you plan to manipulate
 *       integers in a tight loop you're advised to use the underlying BN.js value or
 *       convert to a JavaScript number first.
 */
declare class Int implements ABISerializableObject {
    static abiName: string;
    static isSigned: boolean;
    static byteWidth: number;
    /** Largest value that can be represented by this integer type. */
    static get max(): BN;
    /** Smallest value that can be represented by this integer type. */
    static get min(): BN;
    /** Add `lhs` to `rhs` and return the resulting value. */
    static add(lhs: Int, rhs: Int, overflow?: OverflowBehavior): Int;
    /** Add `lhs` to `rhs` and return the resulting value. */
    static sub(lhs: Int, rhs: Int, overflow?: OverflowBehavior): Int;
    /** Multiply `lhs` by `rhs` and return the resulting value. */
    static mul(lhs: Int, rhs: Int, overflow?: OverflowBehavior): Int;
    /**
     * Divide `lhs` by `rhs` and return the quotient, dropping the remainder.
     * @throws When dividing by zero.
     */
    static div(lhs: Int, rhs: Int, overflow?: OverflowBehavior): Int;
    /**
     * Divide `lhs` by `rhs` and return the quotient + remainder rounded to the closest integer.
     * @throws When dividing by zero.
     */
    static divRound(lhs: Int, rhs: Int, overflow?: OverflowBehavior): Int;
    /**
     * Divide `lhs` by `rhs` and return the quotient + remainder rounded up to the closest integer.
     * @throws When dividing by zero.
     */
    static divCeil(lhs: Int, rhs: Int, overflow?: OverflowBehavior): Int;
    /**
     * Can be used to implement custom operator.
     * @internal
     */
    static operator(lhs: Int, rhs: Int, overflow: OverflowBehavior | undefined, fn: (lhs: BN, rhs: BN) => BN): Int;
    /**
     * Create a new instance from value.
     * @param value Value to create new Int instance from, can be a string, number,
     *              little-endian byte array or another Int instance.
     * @param overflow How to handle integer overflow, default behavior is to throw.
     */
    static from<T extends typeof Int>(this: T, value: IntType | Uint8Array, overflow?: OverflowBehavior): InstanceType<T>;
    static from(value: any, overflow?: OverflowBehavior): unknown;
    static fromABI<T extends typeof Int>(this: T, decoder: ABIDecoder): InstanceType<T>;
    static fromABI(decoder: ABIDecoder): unknown;
    static random<T extends typeof Int>(this: T): InstanceType<T>;
    static random(): unknown;
    /**
     * The underlying BN.js instance – don't modify this
     * directly – take a copy first using `.clone()`.
     */
    value: BN;
    /**
     * Create a new instance, don't use this directly. Use the `.from` factory method instead.
     * @throws If the value over- or under-flows the integer type.
     */
    constructor(value: BN);
    /**
     * Cast this integer to other type.
     * @param overflow How to handle overflow, default is to preserve bit-pattern (C++11 behavior).
     */
    cast<T extends typeof Int>(type: T, overflow?: OverflowBehavior): InstanceType<T>;
    /** Number as bytes in little endian (matches memory layout in C++ contract). */
    get byteArray(): Uint8Array;
    /**
     * Compare two integers, if strict is set to true the test will only consider integers
     * of the exact same type. I.e. Int64.from(1).equals(UInt64.from(1)) will return false.
     */
    equals(other: IntType | Uint8Array, strict?: boolean): boolean;
    /** Mutating add. */
    add(num: IntType): void;
    /** Non-mutating add. */
    adding(num: IntType): this;
    /** Mutating subtract. */
    subtract(num: IntType): void;
    /** Non-mutating subtract. */
    subtracting(num: IntType): this;
    /** Mutating multiply. */
    multiply(by: IntType): void;
    /** Non-mutating multiply. */
    multiplying(by: IntType): this;
    /**
     * Mutating divide.
     * @param behavior How to handle the remainder, default is to floor (round down).
     * @throws When dividing by zero.
     */
    divide(by: IntType, behavior?: DivisionBehavior): void;
    /**
     * Non-mutating divide.
     * @param behavior How to handle the remainder, default is to floor (round down).
     * @throws When dividing by zero.
     */
    dividing(by: IntType, behavior?: DivisionBehavior): this;
    /**
     * Run operator with C++11 implicit conversion.
     * @internal
     */
    private operator;
    /**
     * Convert to a JavaScript number.
     * @throws If the number cannot be represented by 53-bits.
     **/
    toNumber(): number;
    toString(): string;
    [Symbol.toPrimitive](type: string): string | number;
    toABI(encoder: ABIEncoder): void;
    toJSON(): string | number;
}
declare type Int8Type = Int8 | IntType;
declare class Int8 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type Int16Type = Int16 | IntType;
declare class Int16 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type Int32Type = Int32 | IntType;
declare class Int32 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type Int64Type = Int64 | IntType;
declare class Int64 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type Int128Type = Int128 | IntType;
declare class Int128 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type UInt8Type = UInt8 | IntType;
declare class UInt8 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type UInt16Type = UInt16 | IntType;
declare class UInt16 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type UInt32Type = UInt32 | IntType;
declare class UInt32 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type UInt64Type = UInt64 | IntType;
declare class UInt64 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type UInt128Type = UInt128 | IntType;
declare class UInt128 extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
}
declare type VarIntType = VarInt | IntType;
declare class VarInt extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
    static fromABI(decoder: ABIDecoder): VarInt;
    toABI(encoder: ABIEncoder): void;
}
declare type VarUIntType = VarUInt | IntType;
declare class VarUInt extends Int {
    static abiName: string;
    static byteWidth: number;
    static isSigned: boolean;
    static fromABI(decoder: ABIDecoder): VarUInt;
    toABI(encoder: ABIEncoder): void;
}
declare type AnyInt = Int8Type | Int16Type | Int32Type | Int64Type | Int128Type | UInt8Type | UInt16Type | UInt32Type | UInt64Type | UInt128Type | VarIntType | VarUIntType;

interface StructConstructor extends ABISerializableConstructor {
    new <T extends Struct>(...args: any[]): T;
    structFields: ABIField[];
}
declare class Struct implements ABISerializableObject {
    static abiName: string;
    static abiFields: ABIField[];
    static abiBase: ABISerializableConstructor;
    static from<T extends StructConstructor>(this: T, value: any): InstanceType<T>;
    static from(value: any): unknown;
    static get structFields(): ABIField[];
    /** @internal */
    constructor(object: any);
    /**
     * Return true if this struct equals the other.
     *
     * Note: This compares the ABI encoded bytes of both structs, subclasses
     *       should implement their own fast equality check when possible.
     */
    equals(other: any): boolean;
    /** @internal */
    toJSON(): any;
}
declare namespace Struct {
    function type(name: string): <T extends StructConstructor>(struct: T) => T;
    function field(type: ABISerializableConstructor | string, options?: Partial<ABIField>): <T extends Struct>(target: T, name: string) => void;
}

declare function TypeAlias(name: string): (typeAlias: any) => any;

interface VariantConstructor extends ABISerializableConstructor {
    new <T extends Variant>(...args: any[]): T;
}
declare type AnyVariant = Variant | ABISerializable | [string, any];
declare class Variant implements ABISerializableObject {
    static abiName: string;
    static abiVariant: ABITypeDescriptor[];
    static from<T extends VariantConstructor>(this: T, object: AnyVariant): InstanceType<T>;
    static from(object: AnyVariant): unknown;
    value: ABISerializable;
    variantIdx: number;
    /** @internal */
    constructor(variant: [string, ABISerializable]);
    /**
     * Return true if this variant equals the other.
     *
     * Note: This compares the ABI encoded bytes of both variants, subclasses
     *       should implement their own fast equality check when possible.
     */
    equals(other: AnyVariant): boolean;
    get variantName(): string;
    /** @internal */
    toJSON(): ABISerializable[];
}
declare namespace Variant {
    function type(name: string, types: ABISerializableType[]): <T extends VariantConstructor>(variant: T) => T;
}

declare type FloatType = Float | number | string;
declare class Float implements ABISerializableObject {
    static abiName: string;
    static byteWidth: number;
    static from<T extends typeof Float>(this: T, value: FloatType): InstanceType<T>;
    static from(value: FloatType): unknown;
    static fromABI<T extends typeof Float>(this: T, decoder: ABIDecoder): InstanceType<T>;
    static fromABI(decoder: ABIDecoder): unknown;
    static random<T extends typeof Float>(this: T): InstanceType<T>;
    static random(): unknown;
    value: number;
    constructor(value: number);
    equals(other: FloatType): boolean;
    toABI(encoder: ABIEncoder): void;
    toString(): string;
    toJSON(): string;
}
declare type Float32Type = Float32 | FloatType;
declare class Float32 extends Float {
    static abiName: string;
    static byteWidth: number;
    toString(): string;
}
declare type Float64Type = Float64 | FloatType;
declare class Float64 extends Float {
    static abiName: string;
    static byteWidth: number;
}
declare type Float128Type = Float128 | BytesType;
declare class Float128 implements ABISerializableObject {
    static abiName: string;
    static byteWidth: number;
    static from(value: Float128Type): Float128;
    static fromABI(decoder: ABIDecoder): Float128;
    static random(): Float128;
    data: Bytes;
    constructor(data: Bytes);
    equals(other: Float128Type): boolean;
    toABI(encoder: ABIEncoder): void;
    toString(): string;
    toJSON(): string;
}

/** Type representing a name. */
declare type NameType = Name | UInt64 | string;
/** EOSIO Name */
declare class Name implements ABISerializableObject {
    static abiName: string;
    /** Regex pattern matching a EOSIO name, case-sensitive. */
    static pattern: RegExp;
    /** The numeric representation of the name. */
    value: UInt64;
    /**
     * The raw representation of the name.
     * @deprecated Use value instead.
     */
    get rawValue(): UInt64;
    /** Create a new Name instance from any of its representing types. */
    static from(value: NameType): Name;
    static fromABI(decoder: ABIDecoder): Name;
    constructor(value: UInt64);
    /** Return true if this name is equal to passed name. */
    equals(other: NameType): boolean;
    /** Return string representation of this name. */
    toString(): string;
    toABI(encoder: ABIEncoder): void;
    /** @internal */
    toJSON(): string;
}

declare type TimePointType = TimePoint | TimePointSec | string | Date | AnyInt;
interface TimePointConstructor {
    from(value: TimePointType): TimePointBase;
    fromInteger(value: AnyInt): TimePointBase;
    fromDate(value: Date): TimePointBase;
    fromString(value: string): TimePointBase;
    fromMilliseconds(value: number): TimePointBase;
    new (...args: any[]): TimePointBase;
}
declare class TimePointBase implements ABISerializableObject {
    static abiName: string;
    static from<T extends TimePointConstructor>(this: T, value: TimePointType): InstanceType<T>;
    static from(value: TimePointType): unknown;
    static fromString<T extends TimePointConstructor>(this: T, string: string): InstanceType<T>;
    static fromString(string: string): unknown;
    static fromDate<T extends TimePointConstructor>(this: T, date: Date): InstanceType<T>;
    static fromDate(date: Date): unknown;
    toABI(encoder: ABIEncoder): void;
    equals(other: TimePointType): boolean;
    toMilliseconds(): number;
    toDate(): Date;
    toJSON(): string;
}
/** Timestamp with microsecond accuracy. */
declare class TimePoint extends TimePointBase {
    static abiName: string;
    static fromMilliseconds(ms: number): TimePoint;
    static fromInteger(value: Int64Type): TimePoint;
    static fromABI(decoder: ABIDecoder): TimePoint;
    value: Int64;
    constructor(value: Int64);
    toString(): string;
    toMilliseconds(): number;
}
/** Timestamp with second accuracy. */
declare class TimePointSec extends TimePointBase {
    static abiName: string;
    static fromMilliseconds(ms: number): TimePointSec;
    static fromInteger(value: UInt32Type): TimePointSec;
    static fromABI(decoder: ABIDecoder): TimePointSec;
    value: UInt32;
    constructor(value: UInt32);
    toString(): string;
    toMilliseconds(): number;
}
declare class BlockTimestamp extends TimePointBase {
    static abiName: string;
    static fromMilliseconds(ms: number): BlockTimestamp;
    static fromInteger(value: UInt32Type): BlockTimestamp;
    static fromABI(decoder: ABIDecoder): BlockTimestamp;
    value: UInt32;
    constructor(value: UInt32);
    toString(): string;
    toMilliseconds(): number;
}

declare type ABIDef = string | Partial<ABI.Def> | ABI;
declare class ABI implements ABISerializableObject {
    static abiName: string;
    static version: string;
    version: string;
    types: ABI.TypeDef[];
    variants: ABI.Variant[];
    structs: ABI.Struct[];
    actions: ABI.Action[];
    tables: ABI.Table[];
    ricardian_clauses: ABI.Clause[];
    constructor(args: Partial<ABI.Def>);
    static from(value: ABIDef): ABI;
    static fromABI(decoder: ABIDecoder): ABI;
    toABI(encoder: ABIEncoder): void;
    resolveType(name: string): ABI.ResolvedType;
    resolveAll(): {
        types: ABI.ResolvedType[];
        variants: ABI.ResolvedType[];
        structs: ABI.ResolvedType[];
    };
    private resolve;
    getStruct(name: string): ABI.Struct | undefined;
    getVariant(name: string): ABI.Variant | undefined;
    /** Return arguments type of an action in this ABI. */
    getActionType(actionName: NameType): string | undefined;
    equals(other: ABIDef): boolean;
    toJSON(): {
        version: string;
        types: ABI.TypeDef[];
        structs: ABI.Struct[];
        actions: ABI.Action[];
        tables: ABI.Table[];
        ricardian_clauses: ABI.Clause[];
        error_messages: never[];
        abi_extensions: never[];
        variants: ABI.Variant[];
    };
}
declare namespace ABI {
    interface TypeDef {
        new_type_name: string;
        type: string;
    }
    interface Field {
        name: string;
        type: string;
    }
    interface Struct {
        name: string;
        base: string;
        fields: Field[];
    }
    interface Action {
        name: NameType;
        type: string;
        ricardian_contract: string;
    }
    interface Table {
        name: NameType;
        index_type: string;
        key_names: string[];
        key_types: string[];
        type: string;
    }
    interface Clause {
        id: string;
        body: string;
    }
    interface Variant {
        name: string;
        types: string[];
    }
    interface Def {
        version: string;
        types: TypeDef[];
        variants: Variant[];
        structs: Struct[];
        actions: Action[];
        tables: Table[];
        ricardian_clauses: Clause[];
    }
    class ResolvedType {
        name: string;
        id: number;
        isArray: boolean;
        isOptional: boolean;
        isExtension: boolean;
        base?: ResolvedType;
        fields?: {
            name: string;
            type: ResolvedType;
        }[];
        variant?: ResolvedType[];
        ref?: ResolvedType;
        constructor(fullName: string, id?: number);
        /**
         * Type name including suffixes: [] array, ? optional, $ binary ext
         */
        get typeName(): string;
        /** All fields including base struct(s), undefined if not a struct type. */
        get allFields(): {
            name: string;
            type: ResolvedType;
        }[] | undefined;
    }
}

declare type AssetType = Asset | string;
declare class Asset implements ABISerializableObject {
    static abiName: string;
    units: Int64;
    symbol: Asset.Symbol;
    static from(value: AssetType): Asset;
    static from(value: number, symbol: Asset.SymbolType): Asset;
    static fromString(value: string): Asset;
    static fromFloat(value: number, symbol: Asset.SymbolType): Asset;
    static fromUnits(value: Int64Type, symbol: Asset.SymbolType): Asset;
    static fromABI(decoder: ABIDecoder): Asset;
    constructor(units: Int64, symbol: Asset.Symbol);
    equals(other: AssetType): boolean;
    get value(): number;
    set value(newValue: number);
    toABI(encoder: ABIEncoder): void;
    toString(): string;
    toJSON(): string;
}
declare namespace Asset {
    type SymbolType = Symbol | UInt64 | string;
    class Symbol implements ABISerializableObject {
        static abiName: string;
        static symbolNamePattern: RegExp;
        static maxPrecision: number;
        static from(value: SymbolType): Symbol;
        static fromParts(name: string, precision: number): Symbol;
        static fromABI(decoder: ABIDecoder): Symbol;
        value: UInt64;
        constructor(value: UInt64);
        equals(other: SymbolType): boolean;
        get name(): string;
        get precision(): number;
        get code(): SymbolCode;
        toABI(encoder: ABIEncoder): void;
        /**
         * Convert units to floating point number according to symbol precision.
         * @throws If the given units can't be represented in 53 bits.
         **/
        convertUnits(units: Int64): number;
        /**
         * Convert floating point to units according to symbol precision.
         * Note that the value will be rounded to closest precision.
         **/
        convertFloat(float: number): Int64;
        toString(): string;
        toJSON(): string;
    }
    type SymbolCodeType = SymbolCode | UInt64 | string | number;
    class SymbolCode implements ABISerializableObject {
        static abiName: string;
        static from(value: SymbolCodeType): SymbolCode;
        static fromABI(decoder: ABIDecoder): SymbolCode;
        value: UInt64;
        constructor(value: UInt64);
        equals(other: SymbolCodeType): boolean;
        toABI(encoder: ABIEncoder): void;
        toString(): string;
        toJSON(): string;
    }
}
declare type ExtendedAssetType = ExtendedAsset | {
    quantity: AssetType;
    contract: NameType;
};
declare class ExtendedAsset implements ABISerializableObject {
    static abiName: string;
    static from(value: ExtendedAssetType): ExtendedAsset;
    static fromABI(decoder: ABIDecoder): ExtendedAsset;
    quantity: Asset;
    contract: Name;
    constructor(quantity: Asset, contract: Name);
    equals(other: ExtendedAssetType): boolean;
    toABI(encoder: ABIEncoder): void;
    toJSON(): {
        quantity: Asset;
        contract: Name;
    };
}

declare type PublicKeyType = PublicKey | string | {
    type: string;
    compressed: Uint8Array;
};
declare class PublicKey implements ABISerializableObject {
    static abiName: string;
    /** Type, e.g. `K1` */
    type: KeyType;
    /** Compressed public key point. */
    data: Bytes;
    /** Create PublicKey object from representing types. */
    static from(value: PublicKeyType): PublicKey;
    /** @internal */
    static fromABI(decoder: ABIDecoder): PublicKey;
    /** @internal */
    constructor(type: KeyType, data: Bytes);
    equals(other: PublicKeyType): boolean;
    /**
     * Return EOSIO legacy (`EOS<base58data>`) formatted key.
     * @throws If the key type isn't `K1`
     */
    toLegacyString(prefix?: string): string;
    /** Return key in modern EOSIO format (`PUB_<type>_<base58data>`) */
    toString(): string;
    /** @internal */
    toABI(encoder: ABIEncoder): void;
    /** @internal */
    toJSON(): string;
}

declare type SignatureType = Signature | string | {
    type: string;
    r: Uint8Array;
    s: Uint8Array;
    recid: number;
};
declare class Signature implements ABISerializableObject {
    static abiName: string;
    /** Type, e.g. `K1` */
    type: KeyType;
    /** Signature data. */
    data: Bytes;
    /** Create Signature object from representing types. */
    static from(value: SignatureType): Signature;
    /** @internal */
    static fromABI(decoder: ABIDecoder): Signature;
    /** @internal */
    constructor(type: KeyType, data: Bytes);
    equals(other: SignatureType): boolean;
    /** Recover public key from given message digest. */
    recoverDigest(digest: Checksum256Type): PublicKey;
    /** Recover public key from given message. */
    recoverMessage(message: BytesType): PublicKey;
    /** Verify this signature with given message digest and public key. */
    verifyDigest(digest: Checksum256Type, publicKey: PublicKey): boolean;
    /** Verify this signature with given message and public key. */
    verifyMessage(message: BytesType, publicKey: PublicKey): boolean;
    /** Base58check encoded string representation of this signature (`SIG_<type>_<data>`). */
    toString(): string;
    /** @internal */
    toABI(encoder: ABIEncoder): void;
    /** @internal */
    toJSON(): string;
}

declare type PrivateKeyType = PrivateKey | string;
declare class PrivateKey {
    type: KeyType;
    data: Bytes;
    /** Create PrivateKey object from representing types. */
    static from(value: PrivateKeyType): PrivateKey;
    /**
     * Create PrivateKey object from a string representation.
     * Accepts WIF (5...) and EOSIO (PVT_...) style private keys.
     */
    static fromString(string: string, ignoreChecksumError?: boolean): PrivateKey;
    /**
     * Generate new PrivateKey.
     * @throws If a secure random source isn't available.
     */
    static generate(type: KeyType | string): PrivateKey;
    /** @internal */
    constructor(type: KeyType, data: Bytes);
    /**
     * Sign message digest using this key.
     * @throws If the key type isn't R1 or K1.
     */
    signDigest(digest: Checksum256Type): Signature;
    /**
     * Sign message using this key.
     * @throws If the key type isn't R1 or K1.
     */
    signMessage(message: BytesType): Signature;
    /**
     * Derive the shared secret between this private key and given public key.
     * @throws If the key type isn't R1 or K1.
     */
    sharedSecret(publicKey: PublicKey): Checksum512;
    /**
     * Get the corresponding public key.
     * @throws If the key type isn't R1 or K1.
     */
    toPublic(): PublicKey;
    /**
     * Return WIF representation of this private key
     * @throws If the key type isn't K1.
     */
    toWif(): string;
    /**
     * Return the key in EOSIO PVT_<type>_<base58check> format.
     */
    toString(): string;
    toJSON(): string;
}

declare type PermissionLevelType = PermissionLevel | {
    actor: NameType;
    permission: NameType;
};
/** EOSIO Permission Level, a.k.a "auth". */
declare class PermissionLevel extends Struct {
    actor: Name;
    permission: Name;
    /** Create new permission level from representing types. Can be expressed as a string in the format `<actor>@<permission>`. */
    static from(value: PermissionLevelType | string): PermissionLevel;
    /** Return true if this permission level equals other. */
    equals(other: PermissionLevelType | string): boolean;
    toString(): string;
}

interface ActionBase {
    /** The account (a.k.a. contract) to run action on. */
    account: NameType;
    /** The name of the action. */
    name: NameType;
    /** The permissions authorizing the action. */
    authorization: PermissionLevelType[];
}
interface ActionFields extends ActionBase {
    /** The ABI-encoded action data. */
    data: BytesType;
}
/** Action type that may or may not have its data encoded */
interface AnyAction extends ActionBase {
    data: BytesType | ABISerializableObject | Record<string, any>;
}
declare type ActionType = Action | ActionFields;
declare class Action extends Struct {
    /** The account (a.k.a. contract) to run action on. */
    account: Name;
    /** The name of the action. */
    name: Name;
    /** The permissions authorizing the action. */
    authorization: PermissionLevel[];
    /** The ABI-encoded action data. */
    data: Bytes;
    static from(object: ActionType | AnyAction, abi?: ABIDef): Action;
    /** Return true if this Action is equal to given action. */
    equals(other: ActionType | AnyAction): boolean;
    /** Return action data decoded as given type or using ABI. */
    decodeData<T extends ABISerializableConstructor>(type: T): InstanceType<T>;
    decodeData<T extends keyof BuiltinTypes>(type: T): BuiltinTypes[T];
    decodeData(abi: ABIDef): ABISerializable;
}

declare class TransactionExtension extends Struct {
    type: UInt16;
    data: Bytes;
}
interface TransactionHeaderFields {
    /** The time at which a transaction expires. */
    expiration: TimePointType;
    /** *Specifies a block num in the last 2^16 blocks. */
    ref_block_num: UInt16Type;
    /** Specifies the lower 32 bits of the block id. */
    ref_block_prefix: UInt32Type;
    /** Upper limit on total network bandwidth (in 8 byte words) billed for this transaction. */
    max_net_usage_words?: VarUIntType;
    /** Upper limit on the total CPU time billed for this transaction. */
    max_cpu_usage_ms?: UInt8Type;
    /** Number of seconds to delay this transaction for during which it may be canceled. */
    delay_sec?: VarUIntType;
}
declare type TransactionHeaderType = TransactionHeader | TransactionHeaderFields;
declare class TransactionHeader extends Struct {
    /** The time at which a transaction expires. */
    expiration: TimePointSec;
    /** *Specifies a block num in the last 2^16 blocks. */
    ref_block_num: UInt16;
    /** Specifies the lower 32 bits of the block id. */
    ref_block_prefix: UInt32;
    /** Upper limit on total network bandwidth (in 8 byte words) billed for this transaction. */
    max_net_usage_words: VarUInt;
    /** Upper limit on the total CPU time billed for this transaction. */
    max_cpu_usage_ms: UInt8;
    /** Number of seconds to delay this transaction for during which it may be canceled. */
    delay_sec: VarUInt;
    static from(object: TransactionHeaderType): TransactionHeader;
}
interface TransactionFields extends TransactionHeaderFields {
    /** The context free actions in the transaction. */
    context_free_actions?: ActionType[];
    /** The actions in the transaction. */
    actions?: ActionType[];
    /** Transaction extensions. */
    transaction_extensions?: {
        type: UInt16Type;
        data: BytesType;
    }[];
}
interface AnyTransaction extends TransactionHeaderFields {
    /** The context free actions in the transaction. */
    context_free_actions?: AnyAction[];
    /** The actions in the transaction. */
    actions?: AnyAction[];
    /** Transaction extensions. */
    transaction_extensions?: {
        type: UInt16Type;
        data: BytesType;
    }[];
}
declare type TransactionType = Transaction | TransactionFields;
declare class Transaction extends TransactionHeader {
    /** The context free actions in the transaction. */
    context_free_actions: Action[];
    /** The actions in the transaction. */
    actions: Action[];
    /** Transaction extensions. */
    transaction_extensions: TransactionExtension[];
    static from(object: TransactionType | AnyTransaction, abis?: ABIDef | {
        contract: NameType;
        abi: ABIDef;
    }[]): Transaction;
    /** Return true if this transaction is equal to given transaction. */
    equals(other: TransactionType): boolean;
    get id(): Checksum256;
    signingDigest(chainId: Checksum256Type): Checksum256;
    signingData(chainId: Checksum256Type): Bytes;
}
interface SignedTransactionFields extends TransactionFields {
    /** List of signatures. */
    signatures?: SignatureType[];
    /** Context-free action data, for each context-free action, there is an entry here. */
    context_free_data?: BytesType[];
}
declare type SignedTransactionType = SignedTransaction | SignedTransactionFields;
declare class SignedTransaction extends Transaction {
    /** List of signatures. */
    signatures: Signature[];
    /** Context-free action data, for each context-free action, there is an entry here. */
    context_free_data: Bytes[];
    static from(object: SignedTransactionType): SignedTransaction;
}
declare class PackedTransaction extends Struct {
    signatures: Signature[];
    compression: UInt8;
    packed_context_free_data: Bytes;
    packed_trx: Bytes;
    static fromSigned(signed: SignedTransaction): PackedTransaction;
    getTransaction(): Transaction;
    getSignedTransaction(): SignedTransaction;
}
declare class TransactionReceipt extends Struct {
    status: string;
    cpu_usage_us: UInt32;
    net_usage_words: UInt32;
}

declare class Weight extends UInt16 {
}
declare class KeyWeight extends Struct {
    key: PublicKey;
    weight: Weight;
}
declare class PermissionLevelWeight extends Struct {
    permission: PermissionLevel;
    weight: Weight;
}
declare class WaitWeight extends Struct {
    wait_sec: UInt32;
    weight: Weight;
}
declare type AuthorityType = Authority | {
    threshold: UInt32Type;
    keys?: {
        key: PublicKeyType;
        weight: UInt16Type;
    }[];
    accounts?: {
        permission: PermissionLevelType;
        weight: UInt16Type;
    }[];
    waits?: {
        wait_sec: UInt32Type;
        weight: UInt16Type;
    }[];
};
declare class Authority extends Struct {
    threshold: UInt32;
    keys: KeyWeight[];
    accounts: PermissionLevelWeight[];
    waits: WaitWeight[];
    static from(value: AuthorityType): Authority;
    /** Total weight of all waits. */
    get waitThreshold(): number;
    /** Weight a key needs to sign for this authority. */
    get keyThreshold(): number;
    /** Return the weight for given public key, or zero if it is not included in this authority. */
    keyWeight(publicKey: PublicKeyType): number;
    /**
     * Check if given public key has permission in this authority,
     * @attention Does not take indirect permissions for the key via account weights into account.
     * @param publicKey The key to check.
     * @param includePartial Whether to consider auths where the key is included but can't be reached alone (e.g. multisig).
     */
    hasPermission(publicKey: PublicKeyType, includePartial?: boolean): boolean;
    /**
     * Sorts the authority weights in place, should be called before including the authority in a `updateauth` action or it might be rejected.
     */
    sort(): void;
}

declare namespace Serializer {
    const encode: typeof abiEncode;
    const decode: typeof abiDecode;
    /** Create an EOSIO ABI definition for given core type. */
    function synthesize(type: ABISerializableConstructor): ABI;
    /** Create JSON representation of a core object. */
    function stringify(object: ABISerializable): string;
    /** Create a vanilla js representation of a core object. */
    function objectify(object: ABISerializable): any;
}

declare namespace Base58 {
    enum ErrorCode {
        E_CHECKSUM = "E_CHECKSUM",
        E_INVALID = "E_INVALID"
    }
    class DecodingError extends Error {
        readonly code: ErrorCode;
        readonly info: Record<string, any>;
        static __className: string;
        constructor(message: string, code: ErrorCode, info?: Record<string, any>);
    }
    /** Decode a Base58 encoded string. */
    function decode(s: string, size?: number): Bytes;
    /** Decode a Base58Check encoded string. */
    function decodeCheck(encoded: string, size?: number): Bytes;
    /** Decode a Base58Check encoded string that uses ripemd160 instead of double sha256 for the digest. */
    function decodeRipemd160Check(encoded: string, size?: number, suffix?: string): Bytes;
    /** Encode bytes to a Base58 string.  */
    function encode(data: BytesType): string;
    function encodeCheck(data: BytesType): string;
    function encodeRipemd160Check(data: BytesType, suffix?: string): string;
}

/** Check if object in instance of class. */
declare function isInstanceOf<T extends {
    new (...args: any[]): InstanceType<T>;
}>(object: any, someClass: T): object is InstanceType<T>;

declare type Fetch = (input: any, init?: any) => Promise<any>;
/** Response to an API call.  */
interface APIResponse {
    json?: any;
    text: string;
    status: number;
    headers: Record<string, string>;
}
interface APIProvider {
    /**
     * Call an API endpoint and return the response.
     * Provider is responsible for JSON encoding the params and decoding the response.
     * @argument path The endpoint path, e.g. `/v1/chain/get_info`
     * @argument params The request body if any.
     */
    call(path: string, params?: unknown): Promise<APIResponse>;
}
interface FetchProviderOptions {
    /**
     * Fetch instance, must be provided in non-browser environments.
     * You can use the node-fetch package in Node.js.
     */
    fetch?: Fetch;
}
/** Default provider that uses the Fetch API to call a single node. */
declare class FetchProvider implements APIProvider {
    readonly url: string;
    readonly fetch: Fetch;
    constructor(url: string, options?: FetchProviderOptions);
    call(path: string, params?: unknown): Promise<{
        headers: {};
        status: any;
        json: any;
        text: any;
    }>;
}

declare class AccountPermission extends Struct {
    perm_name: Name;
    parent: Name;
    required_auth: Authority;
}
declare class AccountResourceLimit extends Struct {
    used: Int64;
    available: Int64;
    max: Int64;
}
declare class AccountTotalResources extends Struct {
    owner: Name;
    net_weight: Asset;
    cpu_weight: Asset;
    ram_bytes: UInt64;
}
declare class AccountSelfDelegatedBandwidth extends Struct {
    from: Name;
    to: Name;
    net_weight: Asset;
    cpu_weight: Asset;
}
declare class AccountRefundRequest extends Struct {
    owner: Name;
    request_time: TimePoint;
    net_amount: Asset;
    cpu_amount: Asset;
}
declare class AccountVoterInfo extends Struct {
    owner: Name;
    proxy: Name;
    producers: Name[];
    staked?: Int64;
    is_proxy: boolean;
    flags1?: UInt32;
    reserved2: UInt32;
    reserved3: string;
}
declare class AccountRexInfoMaturities extends Struct {
    /** Expected results from after EOSIO.Contracts v1.9.0 */
    key?: TimePoint;
    value?: Int64;
    /** Expected results from before EOSIO.Contracts v1.9.0 */
    first?: TimePoint;
    second?: Int64;
}
declare class AccountRexInfo extends Struct {
    version: UInt32;
    owner: Name;
    vote_stake: Asset;
    rex_balance: Asset;
    matured_rex: Int64;
    rex_maturities: AccountRexInfoMaturities[];
}
interface GetAbiResponse {
    account_name: string;
    abi?: ABI.Def;
}
declare class AccountObject extends Struct {
    /** The account name of the retrieved account */
    account_name: Name;
    /** Highest block number on the chain */
    head_block_num: UInt32;
    /** Highest block unix timestamp. */
    head_block_time: TimePoint;
    /** Indicator of if this is a privileged system account */
    privileged: boolean;
    /** Last update to accounts contract as unix timestamp. */
    last_code_update: TimePoint;
    /** Account created as unix timestamp. */
    created: TimePoint;
    /** Account core token balance */
    core_liquid_balance?: Asset;
    ram_quota: Int64;
    net_weight: Int64;
    cpu_weight: Int64;
    net_limit: AccountResourceLimit;
    cpu_limit: AccountResourceLimit;
    ram_usage: UInt64;
    permissions: AccountPermission[];
    total_resources: AccountTotalResources;
    self_delegated_bandwidth?: AccountSelfDelegatedBandwidth;
    refund_request?: AccountRefundRequest;
    voter_info?: AccountVoterInfo;
    rex_info?: AccountRexInfo;
    getPermission(permission: NameType): AccountPermission;
}
declare class NewProducersEntry extends Struct {
    producer_name: Name;
    block_signing_key: PublicKey;
}
declare class NewProducers extends Struct {
    version: UInt32;
    producers: NewProducersEntry;
}
declare class BlockExtension extends Struct {
    type: UInt16;
    data: Bytes;
}
declare class HeaderExtension extends Struct {
    type: UInt16;
    data: Bytes;
}
declare class TrxVariant implements ABISerializableObject {
    readonly id: Checksum256;
    readonly extra: Record<string, any>;
    static abiName: string;
    static from(data: any): TrxVariant;
    constructor(id: Checksum256, extra: Record<string, any>);
    get transaction(): Transaction | undefined;
    get signatures(): Signature[] | undefined;
    equals(other: any): boolean;
    toJSON(): Checksum256;
}
declare class GetBlockResponseTransactionReceipt extends TransactionReceipt {
    trx: TrxVariant;
    get id(): Checksum256;
}
declare class GetBlockResponse extends Struct {
    timestamp: TimePoint;
    producer: Name;
    confirmed: UInt16;
    previous: Checksum256;
    transaction_mroot: Checksum256;
    action_mroot: Checksum256;
    schedule_version: UInt32;
    new_producers?: NewProducers;
    header_extensions?: HeaderExtension[];
    new_protocol_features?: any;
    producer_signature: Signature;
    transactions: GetBlockResponseTransactionReceipt[];
    block_extensions: BlockExtension[];
    id: Checksum256;
    block_num: UInt32;
    ref_block_prefix: UInt32;
}
declare class ActiveScheduleProducerAuthority extends Struct {
    producer_name: Name;
    authority: any;
}
declare class ActiveScheduleProducer extends Struct {
    producer_name: Name;
    authority: ActiveScheduleProducerAuthority;
}
declare class ActiveSchedule extends Struct {
    version: UInt32;
    producers: ActiveScheduleProducer[];
}
declare class BlockStateHeader extends Struct {
    timestamp: TimePoint;
    producer: Name;
    confirmed: UInt16;
    previous: Checksum256;
    transaction_mroot: Checksum256;
    action_mroot: Checksum256;
    schedule_version: UInt32;
    header_extensions?: HeaderExtension[];
    producer_signature: Signature;
}
declare class GetBlockHeaderStateResponse extends Struct {
    block_num: UInt32;
    dpos_proposed_irreversible_blocknum: UInt32;
    dpos_irreversible_blocknum: UInt32;
    id: Checksum256;
    header: BlockStateHeader;
    /** Unstructured any fields specific to header state calls */
    active_schedule: any;
    blockroot_merkle: any;
    producer_to_last_produced: any;
    producer_to_last_implied_irb: any;
    valid_block_signing_authority: any;
    confirm_count: any;
    pending_schedule: any;
    activated_protocol_features: any;
    additional_signatures: any;
}
declare class GetInfoResponse extends Struct {
    /** Hash representing the last commit in the tagged release. */
    server_version: string;
    /** Hash representing the ID of the chain. */
    chain_id: Checksum256;
    /** Highest block number on the chain */
    head_block_num: UInt32;
    /** Highest block number on the chain that has been irreversibly applied to state. */
    last_irreversible_block_num: UInt32;
    /** Highest block ID on the chain that has been irreversibly applied to state. */
    last_irreversible_block_id: Checksum256;
    /** Highest block ID on the chain. */
    head_block_id: Checksum256;
    /** Highest block unix timestamp. */
    head_block_time: TimePoint;
    /** Producer that signed the highest block (head block). */
    head_block_producer: Name;
    /** CPU limit calculated after each block is produced, approximately 1000 times `blockCpuLimit`. */
    virtual_block_cpu_limit: UInt64;
    /** NET limit calculated after each block is produced, approximately 1000 times `blockNetLimit`. */
    virtual_block_net_limit: UInt64;
    /** Actual maximum CPU limit. */
    block_cpu_limit: UInt64;
    /** Actual maximum NET limit. */
    block_net_limit: UInt64;
    /** String representation of server version. */
    server_version_string?: string;
    /** Sequential block number representing the best known head in the fork database tree. */
    fork_db_head_block_num?: UInt32;
    /** Hash representing the best known head in the fork database tree. */
    fork_db_head_block_id?: Checksum256;
    getTransactionHeader(secondsAhead?: number): TransactionHeader;
}
interface PushTransactionResponse {
    transaction_id: string;
    processed: {
        id: string;
        block_num: number;
        block_time: string;
        receipt: {
            status: string;
            cpu_usage_us: number;
            net_usage_words: number;
        };
        elapsed: number;
        net_usage: number;
        scheduled: boolean;
        action_traces: any[];
        account_ram_delta: any;
    };
}
interface TableIndexTypes {
    float128: Float128;
    float64: Float64;
    i128: UInt128;
    i64: UInt64;
    name: Name;
    ripemd160: Checksum160;
    sha256: Checksum256;
}
declare type TableIndexType = Name | UInt64 | UInt128 | Float64 | Checksum256 | Checksum160;
interface GetTableRowsParams<Index = TableIndexType | string> {
    /** The name of the smart contract that controls the provided table. */
    code: NameType;
    /** Name of the table to query. */
    table: NameType;
    /** The account to which this data belongs, if omitted will be set to be same as `code`. */
    scope?: string | TableIndexType;
    /** Lower lookup bound. */
    lower_bound?: Index;
    /** Upper lookup bound. */
    upper_bound?: Index;
    /** How many rows to fetch, defaults to 10 if unset. */
    limit?: UInt32Type;
    /** Whether to iterate records in reverse order. */
    reverse?: boolean;
    /** Position of the index used, defaults to primary. */
    index_position?: 'primary' | 'secondary' | 'tertiary' | 'fourth' | 'fifth' | 'sixth' | 'seventh' | 'eighth' | 'ninth' | 'tenth';
    /**
     * Whether node should try to decode row data using code abi.
     * Determined automatically based the `type` param if omitted.
     */
    json?: boolean;
    /**
     * Set to true to populate the ram_payers array in the response.
     */
    show_payer?: boolean;
}
interface GetTableRowsParamsKeyed<Index = TableIndexType, Key = keyof TableIndexTypes> extends GetTableRowsParams<Index> {
    /** Index key type, determined automatically when passing a typed `upper_bound` or `lower_bound`. */
    key_type: Key;
}
interface GetTableRowsParamsTyped<Index = TableIndexType | string, Row = ABISerializableType> extends GetTableRowsParams<Index> {
    /** Result type for each row. */
    type: Row;
}
interface GetTableRowsResponse<Index = TableIndexType, Row = any> {
    rows: Row[];
    more: boolean;
    ram_payers?: Name[];
    next_key?: Index;
}
interface GetTableByScopeParams {
    code: NameType;
    table?: NameType;
    lower_bound?: string;
    upper_bound?: string;
    limit?: UInt32Type;
    reverse?: boolean;
}
declare class GetTableByScopeResponseRow extends Struct {
    code: Name;
    scope: Name;
    table: Name;
    payer: Name;
    count: UInt32;
}
declare class GetTableByScopeResponse extends Struct {
    rows: GetTableByScopeResponseRow[];
    more: string;
}
declare class OrderedActionsResult extends Struct {
    global_action_seq: UInt64;
    account_action_seq: Int64;
    block_num: UInt32;
    block_time: BlockTimestamp;
    action_trace?: any;
    irrevirsible?: boolean;
}
declare class GetActionsResponse extends Struct {
    actions: OrderedActionsResult[];
    last_irreversible_block: Int32;
    head_block_num: Int32;
    time_limit_exceeded_error?: boolean;
}
declare class TransactionTrace extends Struct {
}
declare class Trx extends Struct {
    actions: AnyAction[];
    context_free_actions: AnyAction[];
    context_free_data: any[];
    delay_sec: number;
    expiration: string;
    max_cpu_usage_ms: number;
    max_net_usage_words: number;
    ref_block_num: number;
    ref_block_prefix: number;
    signatures: string[];
}
declare class TransactionInfo extends Struct {
    receipt: TransactionReceipt;
    trx: Trx;
}
declare class GetTransactionResponse extends Struct {
    id: Checksum256;
    block_num: UInt32;
    block_time: BlockTimestamp;
    last_irreversible_block: UInt32;
    traces?: TransactionTrace[];
    trx: TransactionInfo;
}
declare class GetKeyAccountsResponse extends Struct {
    account_names: Name[];
}
declare class GetControlledAccountsResponse extends Struct {
    controlled_accounts: Name[];
}

type types$1_AccountPermission = AccountPermission;
declare const types$1_AccountPermission: typeof AccountPermission;
type types$1_AccountResourceLimit = AccountResourceLimit;
declare const types$1_AccountResourceLimit: typeof AccountResourceLimit;
type types$1_AccountTotalResources = AccountTotalResources;
declare const types$1_AccountTotalResources: typeof AccountTotalResources;
type types$1_AccountSelfDelegatedBandwidth = AccountSelfDelegatedBandwidth;
declare const types$1_AccountSelfDelegatedBandwidth: typeof AccountSelfDelegatedBandwidth;
type types$1_AccountRefundRequest = AccountRefundRequest;
declare const types$1_AccountRefundRequest: typeof AccountRefundRequest;
type types$1_AccountVoterInfo = AccountVoterInfo;
declare const types$1_AccountVoterInfo: typeof AccountVoterInfo;
type types$1_AccountRexInfoMaturities = AccountRexInfoMaturities;
declare const types$1_AccountRexInfoMaturities: typeof AccountRexInfoMaturities;
type types$1_AccountRexInfo = AccountRexInfo;
declare const types$1_AccountRexInfo: typeof AccountRexInfo;
type types$1_GetAbiResponse = GetAbiResponse;
type types$1_AccountObject = AccountObject;
declare const types$1_AccountObject: typeof AccountObject;
type types$1_NewProducersEntry = NewProducersEntry;
declare const types$1_NewProducersEntry: typeof NewProducersEntry;
type types$1_NewProducers = NewProducers;
declare const types$1_NewProducers: typeof NewProducers;
type types$1_BlockExtension = BlockExtension;
declare const types$1_BlockExtension: typeof BlockExtension;
type types$1_HeaderExtension = HeaderExtension;
declare const types$1_HeaderExtension: typeof HeaderExtension;
type types$1_TrxVariant = TrxVariant;
declare const types$1_TrxVariant: typeof TrxVariant;
type types$1_GetBlockResponseTransactionReceipt = GetBlockResponseTransactionReceipt;
declare const types$1_GetBlockResponseTransactionReceipt: typeof GetBlockResponseTransactionReceipt;
type types$1_GetBlockResponse = GetBlockResponse;
declare const types$1_GetBlockResponse: typeof GetBlockResponse;
type types$1_ActiveScheduleProducerAuthority = ActiveScheduleProducerAuthority;
declare const types$1_ActiveScheduleProducerAuthority: typeof ActiveScheduleProducerAuthority;
type types$1_ActiveScheduleProducer = ActiveScheduleProducer;
declare const types$1_ActiveScheduleProducer: typeof ActiveScheduleProducer;
type types$1_ActiveSchedule = ActiveSchedule;
declare const types$1_ActiveSchedule: typeof ActiveSchedule;
type types$1_BlockStateHeader = BlockStateHeader;
declare const types$1_BlockStateHeader: typeof BlockStateHeader;
type types$1_GetBlockHeaderStateResponse = GetBlockHeaderStateResponse;
declare const types$1_GetBlockHeaderStateResponse: typeof GetBlockHeaderStateResponse;
type types$1_GetInfoResponse = GetInfoResponse;
declare const types$1_GetInfoResponse: typeof GetInfoResponse;
type types$1_PushTransactionResponse = PushTransactionResponse;
type types$1_TableIndexTypes = TableIndexTypes;
type types$1_TableIndexType = TableIndexType;
type types$1_GetTableRowsParams<Index = TableIndexType | string> = GetTableRowsParams<Index>;
type types$1_GetTableRowsParamsKeyed<Index = TableIndexType, Key = keyof TableIndexTypes> = GetTableRowsParamsKeyed<Index, Key>;
type types$1_GetTableRowsParamsTyped<Index = TableIndexType | string, Row = ABISerializableType> = GetTableRowsParamsTyped<Index, Row>;
type types$1_GetTableRowsResponse<Index = TableIndexType, Row = any> = GetTableRowsResponse<Index, Row>;
type types$1_GetTableByScopeParams = GetTableByScopeParams;
type types$1_GetTableByScopeResponseRow = GetTableByScopeResponseRow;
declare const types$1_GetTableByScopeResponseRow: typeof GetTableByScopeResponseRow;
type types$1_GetTableByScopeResponse = GetTableByScopeResponse;
declare const types$1_GetTableByScopeResponse: typeof GetTableByScopeResponse;
type types$1_OrderedActionsResult = OrderedActionsResult;
declare const types$1_OrderedActionsResult: typeof OrderedActionsResult;
type types$1_GetActionsResponse = GetActionsResponse;
declare const types$1_GetActionsResponse: typeof GetActionsResponse;
type types$1_TransactionTrace = TransactionTrace;
declare const types$1_TransactionTrace: typeof TransactionTrace;
type types$1_Trx = Trx;
declare const types$1_Trx: typeof Trx;
type types$1_TransactionInfo = TransactionInfo;
declare const types$1_TransactionInfo: typeof TransactionInfo;
type types$1_GetTransactionResponse = GetTransactionResponse;
declare const types$1_GetTransactionResponse: typeof GetTransactionResponse;
type types$1_GetKeyAccountsResponse = GetKeyAccountsResponse;
declare const types$1_GetKeyAccountsResponse: typeof GetKeyAccountsResponse;
type types$1_GetControlledAccountsResponse = GetControlledAccountsResponse;
declare const types$1_GetControlledAccountsResponse: typeof GetControlledAccountsResponse;
declare namespace types$1 {
  export {
    types$1_AccountPermission as AccountPermission,
    types$1_AccountResourceLimit as AccountResourceLimit,
    types$1_AccountTotalResources as AccountTotalResources,
    types$1_AccountSelfDelegatedBandwidth as AccountSelfDelegatedBandwidth,
    types$1_AccountRefundRequest as AccountRefundRequest,
    types$1_AccountVoterInfo as AccountVoterInfo,
    types$1_AccountRexInfoMaturities as AccountRexInfoMaturities,
    types$1_AccountRexInfo as AccountRexInfo,
    types$1_GetAbiResponse as GetAbiResponse,
    types$1_AccountObject as AccountObject,
    types$1_NewProducersEntry as NewProducersEntry,
    types$1_NewProducers as NewProducers,
    types$1_BlockExtension as BlockExtension,
    types$1_HeaderExtension as HeaderExtension,
    types$1_TrxVariant as TrxVariant,
    types$1_GetBlockResponseTransactionReceipt as GetBlockResponseTransactionReceipt,
    types$1_GetBlockResponse as GetBlockResponse,
    types$1_ActiveScheduleProducerAuthority as ActiveScheduleProducerAuthority,
    types$1_ActiveScheduleProducer as ActiveScheduleProducer,
    types$1_ActiveSchedule as ActiveSchedule,
    types$1_BlockStateHeader as BlockStateHeader,
    types$1_GetBlockHeaderStateResponse as GetBlockHeaderStateResponse,
    types$1_GetInfoResponse as GetInfoResponse,
    types$1_PushTransactionResponse as PushTransactionResponse,
    types$1_TableIndexTypes as TableIndexTypes,
    types$1_TableIndexType as TableIndexType,
    types$1_GetTableRowsParams as GetTableRowsParams,
    types$1_GetTableRowsParamsKeyed as GetTableRowsParamsKeyed,
    types$1_GetTableRowsParamsTyped as GetTableRowsParamsTyped,
    types$1_GetTableRowsResponse as GetTableRowsResponse,
    types$1_GetTableByScopeParams as GetTableByScopeParams,
    types$1_GetTableByScopeResponseRow as GetTableByScopeResponseRow,
    types$1_GetTableByScopeResponse as GetTableByScopeResponse,
    types$1_OrderedActionsResult as OrderedActionsResult,
    types$1_GetActionsResponse as GetActionsResponse,
    types$1_TransactionTrace as TransactionTrace,
    types$1_Trx as Trx,
    types$1_TransactionInfo as TransactionInfo,
    types$1_GetTransactionResponse as GetTransactionResponse,
    types$1_GetKeyAccountsResponse as GetKeyAccountsResponse,
    types$1_GetControlledAccountsResponse as GetControlledAccountsResponse,
  };
}

declare class ChainAPI {
    private client;
    constructor(client: APIClient);
    get_abi(accountName: NameType): Promise<GetAbiResponse>;
    get_account(accountName: NameType): Promise<AccountObject>;
    get_block(block_num_or_id: Checksum256Type | UInt32Type): Promise<GetBlockResponse>;
    get_block_header_state(block_num_or_id: Checksum256Type | UInt32Type): Promise<GetBlockHeaderStateResponse>;
    get_currency_balance(contract: NameType, accountName: NameType, symbol?: string): Promise<Asset[]>;
    get_info(): Promise<GetInfoResponse>;
    push_transaction(tx: SignedTransactionType | PackedTransaction): Promise<PushTransactionResponse>;
    get_table_rows<Index extends TableIndexType = Name>(params: GetTableRowsParams<Index>): Promise<GetTableRowsResponse<Index>>;
    get_table_rows<Key extends keyof TableIndexTypes>(params: GetTableRowsParamsKeyed<TableIndexTypes[Key], Key>): Promise<GetTableRowsResponse<TableIndexTypes[Key]>>;
    get_table_rows<Row extends ABISerializableConstructor, Index extends TableIndexType = Name>(params: GetTableRowsParamsTyped<Index, Row>): Promise<GetTableRowsResponse<Index, InstanceType<Row>>>;
    get_table_rows<Row extends ABISerializableConstructor, Key extends keyof TableIndexTypes>(params: GetTableRowsParamsTyped<TableIndexTypes[Key], Row> & GetTableRowsParamsKeyed<TableIndexTypes[Key], Key>): Promise<GetTableRowsResponse<TableIndexTypes[Key], InstanceType<Row>>>;
    get_table_by_scope(params: GetTableByScopeParams): Promise<GetTableByScopeResponse>;
}

declare class HistoryAPI {
    private client;
    constructor(client: APIClient);
    get_actions(accountName: NameType, pos: Int32Type, offset: Int32Type): Promise<GetActionsResponse>;
    get_transaction(id: Checksum256Type, options?: {
        blockNumHint?: UInt32Type;
        excludeTraces?: boolean;
    }): Promise<GetTransactionResponse>;
    get_key_accounts(publicKey: PublicKeyType): Promise<GetKeyAccountsResponse>;
    get_controlled_accounts(controllingAccount: NameType): Promise<GetControlledAccountsResponse>;
}

interface APIClientOptions extends FetchProviderOptions {
    /** URL to the API node to use, only used if the provider option is not set. */
    url?: string;
    /** API provider to use, if omitted and the url option is set the default provider will be used.  */
    provider?: APIProvider;
}
interface APIErrorDetail {
    message: string;
    file: string;
    line_number: number;
    method: string;
}
interface APIErrorData {
    code: number;
    name: string;
    what: string;
    details: APIErrorDetail[];
}
declare class APIError extends Error {
    static __className: string;
    static formatError(error: APIErrorData): string;
    /** The path to the API that failed, e.g. `/v1/chain/get_info`. */
    readonly path: string;
    /** The full response from the API that failed. */
    readonly response: APIResponse;
    constructor(path: string, response: APIResponse);
    /** The nodeos error object. */
    get error(): APIErrorData | undefined;
    /** The nodeos error name, e.g. `tx_net_usage_exceeded` */
    get name(): string;
    /** The nodeos error code, e.g. `3080002`. */
    get code(): number;
    /** List of exceptions, if any. */
    get details(): APIErrorDetail[];
}
declare class APIClient {
    static __className: string;
    readonly provider: APIProvider;
    constructor(options: APIClientOptions);
    v1: {
        chain: ChainAPI;
        history: HistoryAPI;
    };
    call<T extends ABISerializableConstructor>(args: {
        path: string;
        params?: unknown;
        responseType: T;
    }): Promise<InstanceType<T>>;
    call<T extends keyof BuiltinTypes>(args: {
        path: string;
        params?: unknown;
        responseType: T;
    }): Promise<BuiltinTypes[T]>;
    call<T = unknown>(args: {
        path: string;
        params?: unknown;
    }): Promise<T>;
}

declare namespace types {
  export {
    types$1 as v1,
  };
}

export { ABI, ABIDecoder, ABIDef, ABIEncoder, ABISerializable, ABISerializableConstructor, ABISerializableObject, ABISerializableType, types as API, APIClient, APIClientOptions, APIError, APIErrorData, APIErrorDetail, APIProvider, APIResponse, Action, ActionFields, ActionType, AnyAction, AnyInt, AnyTransaction, AnyVariant, Asset, AssetType, Authority, AuthorityType, Base58, BlockTimestamp, Bytes, BytesEncoding, BytesType, Checksum160, Checksum160Type, Checksum256, Checksum256Type, Checksum512, Checksum512Type, DivisionBehavior, ExtendedAsset, ExtendedAssetType, FetchProvider, FetchProviderOptions, Float128, Float128Type, Float32, Float32Type, Float64, Float64Type, Int, Int128, Int128Type, Int16, Int16Type, Int32, Int32Type, Int64, Int64Type, Int8, Int8Type, KeyType, KeyWeight, Name, NameType, OverflowBehavior, PackedTransaction, PermissionLevel, PermissionLevelType, PermissionLevelWeight, PrivateKey, PrivateKeyType, PublicKey, PublicKeyType, Serializer, Signature, SignatureType, SignedTransaction, SignedTransactionFields, SignedTransactionType, Struct, StructConstructor, TimePoint, TimePointSec, TimePointType, Transaction, TransactionExtension, TransactionFields, TransactionHeader, TransactionHeaderFields, TransactionHeaderType, TransactionReceipt, TransactionType, TypeAlias, UInt128, UInt128Type, UInt16, UInt16Type, UInt32, UInt32Type, UInt64, UInt64Type, UInt8, UInt8Type, VarInt, VarIntType, VarUInt, VarUIntType, Variant, VariantConstructor, WaitWeight, Weight, isInstanceOf };
