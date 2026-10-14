/++
Common floating point math functions.

This module has generic LLVM-oriented API compatible with all D compilers.

$(D pow) follows libm special-value conventions: a base of 1 yields 1 even
for a NaN exponent, and either sign of 1 raised to an infinite exponent
yields 1. For zero or infinite bases, a negative result requires a negative
base and an odd integer exponent; the sign of zero is preserved accordingly.

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors:   Ilia Ki, Phobos Team
+/
module mir.math.common;

import mir.internal.utility: isComplex, isComplexOf, isFloatingPoint;
private import std.traits: Unqual;

// Normalize special values before using Phobos, whose runtime pow can differ
// from LLVM/libm and the compiler's CTFE builtin for these inputs.
private bool powSpecial(T)(in T x, in T power, out Unqual!T result)
    @safe pure nothrow @nogc
    if (isFloatingPoint!T)
{
    import std.math: signbit;

    if (power == 0 || x == 1)
    {
        result = 1;
        return true;
    }
    if (power == T.infinity || power == -T.infinity)
    {
        auto magnitude = x < 0 ? -x : x;
        if (magnitude == 1)
            result = 1;
        else if (magnitude > 1)
            result = power > 0 ? T.infinity : 0;
        else if (magnitude < 1)
            result = power > 0 ? 0 : T.infinity;
        else
            return false; // NaN base: let the backend propagate it.
        return true;
    }
    if ((x == 0 || x == T.infinity || x == -T.infinity)
        && (power > 0 || power < 0))
    {
        // Positive powers keep zero at zero and infinity at infinity;
        // negative powers exchange them.
        result = (x == 0) == (power > 0) ? 0 : T.infinity;
        // Avoid integer casts: real can represent odd integers beyond long.max.
        auto remainder = power % 2;
        if (signbit(x) && (remainder == 1 || remainder == -1))
            result = -result;
        return true;
    }
    return false;
}

version(LDC)
{
    static import ldc.attributes;

    private alias AliasSeq(T...) = T;

    /++
    Functions attribute, an alias for `AliasSeq!(llvmFastMathFlag("contract"));`.
        
    $(UL
    $(LI 1. Allow floating-point contraction (e.g. fusing a multiply followed by an addition into a fused multiply-and-add). )
    )

    Note: Can be used with all compilers.
    +/
    alias fmamath = AliasSeq!(ldc.attributes.llvmFastMathFlag("contract"));

    /++
    Functions attribute, an alias for `AliasSeq!(llvmFastMathFlag("fast"))`.
    
    It is similar to $(LREF fastmath), but does not allow unsafe-fp-math.
    This flag does NOT force LDC to use the reciprocal of an argument rather than perform division.

    This flag is default for string lambdas.

    Note: Can be used with all compilers.
    +/
    alias optmath = AliasSeq!(ldc.attributes.llvmFastMathFlag("fast"));

    /++
    Functions attribute, an alias for `ldc.attributes.fastmath` .
    
    $(UL

    $(LI 1. Enable optimizations that make unsafe assumptions about IEEE math (e.g. that addition is associative) or may not work for all input ranges.
    These optimizations allow the code generator to make use of some instructions which would otherwise not be usable (such as fsin on X86). )

    $(LI 2. Allow optimizations to assume the arguments and result are not NaN.
        Such optimizations are required to retain defined behavior over NaNs,
        but the value of the result is undefined. )

    $(LI 3. Allow optimizations to assume the arguments and result are not +$(BACKTICK)-inf.
        Such optimizations are required to retain defined behavior over +$(BACKTICK)-Inf,
        but the value of the result is undefined. )

    $(LI 4. Allow optimizations to treat the sign of a zero argument or result as insignificant. )

    $(LI 5. Allow optimizations to use the reciprocal of an argument rather than perform division. )

    $(LI 6. Allow floating-point contraction (e.g. fusing a multiply followed by an addition into a fused multiply-and-add). )

    $(LI 7. Allow algebraically equivalent transformations that may dramatically change results in floating point (e.g. reassociate). )
    )
    
    Note: Can be used with all compilers.
    +/
    alias fastmath = ldc.attributes.fastmath;
}
else
enum
{
    /++
    Functions attribute, an alias for `AliasSeq!(llvmFastMathFlag("contract"));`.

    $(UL
    $(LI Allow floating-point contraction (e.g. fusing a multiply followed by an addition into a fused multiply-and-add). )
    )

    Note: Can be used with all compilers.
    +/
    fmamath,

    /++
    Functions attribute, an alias for `AliasSeq!(llvmAttr("unsafe-fp-math", "false"), llvmFastMathFlag("fast"))`.

    It is similar to $(LREF fastmath), but does not allow unsafe-fp-math.
    This flag does NOT force LDC to use the reciprocal of an argument rather than perform division.

    This flag is default for string lambdas.

    Note: Can be used with all compilers.
    +/
    optmath,

    /++
    Functions attribute, an alias for `ldc.attributes.fastmath = AliasSeq!(llvmAttr("unsafe-fp-math", "true"), llvmFastMathFlag("fast"))` .

    $(UL

    $(LI Enable optimizations that make unsafe assumptions about IEEE math (e.g. that addition is associative) or may not work for all input ranges.
    These optimizations allow the code generator to make use of some instructions which would otherwise not be usable (such as fsin on X86). )

    $(LI Allow optimizations to assume the arguments and result are not NaN.
        Such optimizations are required to retain defined behavior over NaNs,
        but the value of the result is undefined. )

    $(LI Allow optimizations to assume the arguments and result are not +$(BACKTICK)-inf.
        Such optimizations are required to retain defined behavior over +$(BACKTICK)-Inf,
        but the value of the result is undefined. )

    $(LI Allow optimizations to treat the sign of a zero argument or result as insignificant. )

    $(LI Allow optimizations to use the reciprocal of an argument rather than perform division. )

    $(LI Allow floating-point contraction (e.g. fusing a multiply followed by an addition into a fused multiply-and-add). )

    $(LI Allow algebraically equivalent transformations that may dramatically change results in floating point (e.g. reassociate). )
    )

    Note: Can be used with all compilers.
    +/
    fastmath
}

version(LDC)
{
    static import ldc.intrinsics;
    static if (__traits(hasMember, ldc.intrinsics, "LLVM_major"))
        private enum llvmMajor = ldc.intrinsics.LLVM_major;
    else
        private enum llvmMajor = ldc.intrinsics.LLVM_version / 100;
    nothrow @nogc pure @safe:

    pragma(LDC_intrinsic, "llvm.sqrt.f#")
    ///
    T sqrt(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.sin.f#")
    ///
    T sin(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.cos.f#")
    ///
    T cos(T)(in T val) if (isFloatingPoint!T);

    static if (llvmMajor >= 13)
        pragma(LDC_intrinsic, "llvm.powi.f#.i32")
        private T llvmPowi(T)(in T val, int power) if (isFloatingPoint!T);
    else 
        pragma(LDC_intrinsic, "llvm.powi.f#")
        private T llvmPowi(T)(in T val, int power) if (isFloatingPoint!T);

    version (CRuntime_Microsoft)
    // Keep LLVM from speculating both pow intrinsics before selecting a result.
    pragma(inline, false)
    private T widePowi(T)(T val, int power) if (isFloatingPoint!T)
    {
        return cast(T) llvmPowi(cast(double) val, power);
    }

    ///
    T powi(T)(in T val, int power) if (isFloatingPoint!T)
    {
        // LLVM power intrinsics cannot be evaluated by CTFE.
        if (__ctfe)
        {
            import std.math: pow;
            return cast(T) pow(val, power);
        }
        version (CRuntime_Microsoft)
        static if (T.mant_dig == float.mant_dig)
        {
            // LLVM lowers float powi to powf on this target, converting the
            // exponent to float. Beyond 2^^24 this can lose integer parity.
            // Double represents every int exactly, including int.min.
            if (power < -0x1000000 || power > 0x1000000)
                return widePowi(val, power);
        }
        return llvmPowi(val, power);
    }

    pragma(LDC_intrinsic, "llvm.pow.f#")
    private T llvmPow(T)(in T val, in T power) if (isFloatingPoint!T);

    ///
    T pow(T)(in T val, in T power) if (isFloatingPoint!T)
    {
        if (__ctfe)
        {
            import std.math: pow;
            Unqual!T result;
            if (powSpecial!T(val, power, result))
                return result;
            return cast(T) pow(val, power);
        }
        return llvmPow(val, power);
    }

    pragma(LDC_intrinsic, "llvm.exp.f#")
    ///
    T exp(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.log.f#")
    ///
    T log(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.fma.f#")
    ///
    T fma(T)(T vala, T valb, T valc) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.fabs.f#")
    ///
    T fabs(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.floor.f#")
    ///
    T floor(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.exp2.f#")
    ///
    T exp2(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.log10.f#")
    ///
    T log10(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.log2.f#")
    ///
    T log2(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.ceil.f#")
    ///
    T ceil(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.trunc.f#")
    ///
    T trunc(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.rint.f#")
    ///
    T rint(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.nearbyint.f#")
    ///
    T nearbyint(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.copysign.f#")
    ///
    T copysign(T)(in T mag, in T sgn) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.round.f#")
    ///
    T round(T)(in T val) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.fmuladd.f#")
    ///
    T fmuladd(T)(in T vala, in T valb, in T valc) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.minnum.f#")
    ///
    T fmin(T)(in T vala, in T valb) if (isFloatingPoint!T);

    pragma(LDC_intrinsic, "llvm.maxnum.f#")
    ///
    T fmax(T)(in T vala, in T valb) if (isFloatingPoint!T);
}
else version(GNU)
{
    static import gcc.builtins;

    // Calls GCC builtin for either float (suffix "f"), double (no suffix), or real (suffix "l").
    private enum mixinGCCBuiltin(string fun) =
    `static if (T.mant_dig == float.mant_dig) return gcc.builtins.__builtin_`~fun~`f(x);`~
    ` else static if (T.mant_dig == double.mant_dig) return gcc.builtins.__builtin_`~fun~`(x);`~
    ` else static if (T.mant_dig == real.mant_dig) return gcc.builtins.__builtin_`~fun~`l(x);`~
    ` else static assert(0);`;

    // As above but for two-argument function.
    private enum mixinGCCBuiltin2(string fun) =
    `static if (T.mant_dig == float.mant_dig) return gcc.builtins.__builtin_`~fun~`f(x, y);`~
    ` else static if (T.mant_dig == double.mant_dig) return gcc.builtins.__builtin_`~fun~`(x, y);`~
    ` else static if (T.mant_dig == real.mant_dig) return gcc.builtins.__builtin_`~fun~`l(x, y);`~
    ` else static assert(0);`;

    ///
    T sqrt(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`sqrt`); }
    ///
    T sin(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`sin`); }
    ///
    T cos(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`cos`); }
    ///
    T pow(T)(in T x, in T power) if (isFloatingPoint!T) { alias y = power; mixin(mixinGCCBuiltin2!`pow`); }
    ///
    T powi(T)(in T x, int power) if (isFloatingPoint!T) { alias y = power; mixin(mixinGCCBuiltin2!`powi`); }
    ///
    T exp(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`exp`); }
    ///
    T log(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`log`); }
    ///
    T fabs(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`fabs`); }
    ///
    T floor(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`floor`); }
    ///
    T exp2(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`exp2`); }
    ///
    T log10(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`log10`); }
    ///
    T log2(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`log2`); }
    ///
    T ceil(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`ceil`); }
    ///
    T trunc(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`trunc`); }
    ///
    T rint(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`rint`); }
    ///
    T nearbyint(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`nearbyint`); }
    ///
    T copysign(T)(in T x, in T sgn) if (isFloatingPoint!T) { alias y = sgn; mixin(mixinGCCBuiltin2!`copysign`); }
    ///
    T round(T)(in T x) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin!`round`); }
    ///
    T fmuladd(T)(in T a, in T b, in T c) if (isFloatingPoint!T)
    {
        static if (T.mant_dig == float.mant_dig)
            return gcc.builtins.__builtin_fmaf(a, b, c);
        else static if (T.mant_dig == double.mant_dig)
            return gcc.builtins.__builtin_fma(a, b, c);
        else static if (T.mant_dig == real.mant_dig)
            return gcc.builtins.__builtin_fmal(a, b, c);
        else
            static assert(0);
    }
    version(mir_core_test)
    unittest { assert(fmuladd!double(2, 3, 4) == 2 * 3 + 4); }
    ///
    T fmin(T)(in T x, in T y) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin2!`fmin`); }
    ///
    T fmax(T)(in T x, in T y) if (isFloatingPoint!T) { mixin(mixinGCCBuiltin2!`fmax`); }
}
else static if (__VERSION__ >= 2082) // DMD 2.082 onward.
{
    static import std.math;
    static import core.stdc.math;

    // Calls either std.math or cmath function for either float (suffix "f")
    // or double (no suffix). std.math will always be used during CTFE or for
    // arguments with greater than double precision or if the cmath function
    // is impure.
    private enum mixinCMath(string fun) =
        `pragma(inline, true);
        static if (!is(typeof(std.math.`~fun~`(0.5f)) == float)
            && is(typeof(() pure => core.stdc.math.`~fun~`f(0.5f))))
        if (!__ctfe)
        {
            static if (T.mant_dig == float.mant_dig) return core.stdc.math.`~fun~`f(x);
            else static if (T.mant_dig == double.mant_dig) return core.stdc.math.`~fun~`(x);
        }
        return std.math.`~fun~`(x);`;

    // As above but for two-argument function (both arguments must be floating point).
    private enum mixinCMath2(string fun) =
        `pragma(inline, true);
        static if (!is(typeof(std.math.`~fun~`(0.5f, 0.5f)) == float)
            && is(typeof(() pure => core.stdc.math.`~fun~`f(0.5f, 0.5f))))
        if (!__ctfe)
        {
            static if (T.mant_dig == float.mant_dig) return core.stdc.math.`~fun~`f(x, y);
            else static if (T.mant_dig == double.mant_dig) return core.stdc.math.`~fun~`(x, y);
        }
        return std.math.`~fun~`(x, y);`;

    // Some std.math functions have appropriate return types (float,
    // double, real) without need for a wrapper. We can alias them
    // directly but we leave the templates afterwards for documentation
    // purposes and so explicit template instantiation still works.
    // The aliases will always match before the templates.
    // Note that you cannot put any "static if" around the aliases or
    // compilation will fail due to conflict with the templates!
    alias sqrt = std.math.sqrt;
    alias sin = std.math.sin;
    alias cos = std.math.cos;
    alias exp = std.math.exp;
    //alias fabs = std.math.fabs;
    alias floor = std.math.floor;
    alias exp2 = std.math.exp2;
    alias ceil = std.math.ceil;
    alias rint = std.math.rint;

    ///
    T sqrt(T)(in T x) if (isFloatingPoint!T) { return std.math.sqrt(x); }
    ///
    T sin(T)(in T x) if (isFloatingPoint!T) { return std.math.sin(x); }
    ///
    T cos(T)(in T x) if (isFloatingPoint!T) { return std.math.cos(x); }
    ///
    T pow(T)(in T x, in T power) if (isFloatingPoint!T)
    {
        Unqual!T result;
        if (powSpecial!T(x, power, result))
            return result;
        alias y = power;
        mixin(mixinCMath2!`pow`);
    }
    ///
    T powi(T)(in T x, int power) if (isFloatingPoint!T) { alias y = power; mixin(mixinCMath2!`pow`); }
    ///
    T exp(T)(in T x) if (isFloatingPoint!T) { return std.math.exp(x); }
    ///
    T log(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`log`); }
    ///
    T fabs(T)(in T x) if (isFloatingPoint!T) { return std.math.fabs(x); }
    ///
    T floor(T)(in T x) if (isFloatingPoint!T) { return std.math.floor(x); }
    ///
    T exp2(T)(in T x) if (isFloatingPoint!T) { return std.math.exp2(x); }
    ///
    T log10(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`log10`); }
    ///
    T log2(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`log2`); }
    ///
    T ceil(T)(in T x) if (isFloatingPoint!T) { return std.math.ceil(x); }
    ///
    T trunc(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`trunc`); }
    ///
    T rint(T)(in T x) if (isFloatingPoint!T) { return std.math.rint(x); }
    ///
    T nearbyint(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`nearbyint`); }
    ///
    T copysign(T)(in T mag, in T sgn) if (isFloatingPoint!T)
    {
        alias x = mag;
        alias y = sgn;
        mixin(mixinCMath2!`copysign`);
    }
    ///
    T round(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`round`); }
    ///
    T fmuladd(T)(in T a, in T b, in T c) if (isFloatingPoint!T) { return a * b + c; }
    version(mir_core_test)
    unittest { assert(fmuladd!double(2, 3, 4) == 2 * 3 + 4); }
    ///
    T fmin(T)(in T x, in T y) if (isFloatingPoint!T)
    {
        version (Windows) // https://issues.dlang.org/show_bug.cgi?id=19798
        {
            version (CRuntime_Microsoft)
                mixin(mixinCMath2!`fmin`);
            else
                return std.math.fmin(x, y);
        }
        else
            mixin(mixinCMath2!`fmin`);
    }
    ///
    T fmax(T)(in T x, in T y) if (isFloatingPoint!T)
    {
        version (Windows) // https://issues.dlang.org/show_bug.cgi?id=19798
        {
            version (CRuntime_Microsoft)
                mixin(mixinCMath2!`fmax`);
            else
                return std.math.fmax(x, y);
        }
        else
            mixin(mixinCMath2!`fmax`);
    }

    version (mir_core_test) @nogc nothrow pure @safe unittest
    {
        // Check the aliases are correct.
        static assert(is(typeof(sqrt(1.0f)) == float));
        static assert(is(typeof(sin(1.0f)) == float));
        static assert(is(typeof(cos(1.0f)) == float));
        static assert(is(typeof(exp(1.0f)) == float));
        static assert(is(typeof(fabs(1.0f)) == float));
        static assert(is(typeof(floor(1.0f)) == float));
        static assert(is(typeof(exp2(1.0f)) == float));
        static assert(is(typeof(ceil(1.0f)) == float));
        static assert(is(typeof(rint(1.0f)) == float));

        auto x = sqrt!float(2.0f); // Explicit template instantiation still works.
        auto fp = &sqrt!float; // Can still take function address.

        // Test for DMD linker problem with fmin on Windows.
        static assert(is(typeof(fmin!float(1.0f, 1.0f))));
        static assert(is(typeof(fmax!float(1.0f, 1.0f))));
    }
}
else // DMD version prior to 2.082
{
    static import std.math;
    static import core.stdc.math;

    // Calls either std.math or cmath function for either float (suffix "f")
    // or double (no suffix). std.math will always be used during CTFE or for
    // arguments with greater than double precision or if the cmath function
    // is impure.
    private enum mixinCMath(string fun) =
        `pragma(inline, true);
        static if (!is(typeof(std.math.`~fun~`(0.5f)) == float)
            && is(typeof(() pure => core.stdc.math.`~fun~`f(0.5f))))
        if (!__ctfe)
        {
            static if (T.mant_dig == float.mant_dig) return core.stdc.math.`~fun~`f(x);
            else static if (T.mant_dig == double.mant_dig) return core.stdc.math.`~fun~`(x);
        }
        return std.math.`~fun~`(x);`;

    // As above but for two-argument function (both arguments must be floating point).
    private enum mixinCMath2(string fun) =
        `pragma(inline, true);
        static if (!is(typeof(std.math.`~fun~`(0.5f, 0.5f)) == float)
            && is(typeof(() pure => core.stdc.math.`~fun~`f(0.5f, 0.5f))))
        if (!__ctfe)
        {
            static if (T.mant_dig == float.mant_dig) return core.stdc.math.`~fun~`f(x, y);
            else static if (T.mant_dig == double.mant_dig) return core.stdc.math.`~fun~`(x, y);
        }
        return std.math.`~fun~`(x, y);`;

    // Some std.math functions have appropriate return types (float,
    // double, real) without need for a wrapper.
    alias sqrt = std.math.sqrt;

    ///
    T sqrt(T)(in T x) if (isFloatingPoint!T) { return std.math.sqrt(x); }
    ///
    T sin(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`sin`); }
    ///
    T cos(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`cos`); }
    ///
    T pow(T)(in T x, in T power) if (isFloatingPoint!T)
    {
        Unqual!T result;
        if (powSpecial!T(x, power, result))
            return result;
        alias y = power;
        mixin(mixinCMath2!`pow`);
    }
    ///
    T powi(T)(in T x, int power) if (isFloatingPoint!T) { alias y = power; mixin(mixinCMath2!`pow`); }
    ///
    T exp(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`exp`); }
    ///
    T log(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`log`); }
    ///
    T fabs(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`fabs`); }
    ///
    T floor(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`floor`); }
    ///
    T exp2(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`exp2`); }
    ///
    T log10(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`log10`); }
    ///
    T log2(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`log2`); }
    ///
    T ceil(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`ceil`); }
    ///
    T trunc(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`trunc`); }
    ///
    T rint(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`rint`); }
    ///
    T nearbyint(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`nearbyint`); }
    ///
    T copysign(T)(in T mag, in T sgn) if (isFloatingPoint!T)
    {
        alias x = mag;
        alias y = sgn;
        mixin(mixinCMath2!`copysign`);
    }
    ///
    T round(T)(in T x) if (isFloatingPoint!T) { mixin(mixinCMath!`round`); }
    ///
    T fmuladd(T)(in T a, in T b, in T c) if (isFloatingPoint!T) { return a * b + c; }
    version(mir_core_test)
    unittest { assert(fmuladd!double(2, 3, 4) == 2 * 3 + 4); }
    ///
    T fmin(T)(in T x, in T y) if (isFloatingPoint!T)
    {
        version (Windows) // https://issues.dlang.org/show_bug.cgi?id=19798
        {
            version (CRuntime_Microsoft)
                mixin(mixinCMath2!`fmin`);
            else
                return std.math.fmin(x, y);
        }
        else
            mixin(mixinCMath2!`fmin`);
    }
    ///
    T fmax(T)(in T x, in T y) if (isFloatingPoint!T)
    {
        version (Windows) // https://issues.dlang.org/show_bug.cgi?id=19798
        {
            version (CRuntime_Microsoft)
                mixin(mixinCMath2!`fmax`);
            else
                return std.math.fmax(x, y);
        }
        else
            mixin(mixinCMath2!`fmax`);
    }

    version (mir_core_test) @nogc nothrow pure @safe unittest
    {
        // Check the aliases are correct.
        static assert(is(typeof(sqrt(1.0f)) == float));
        auto x = sqrt!float(2.0f); // Explicit template instantiation still works.
        auto fp = &sqrt!float; // Can still take function address.

        // Test for DMD linker problem with fmin on Windows.
        static assert(is(typeof(fmin!float(1.0f, 1.0f))));
        static assert(is(typeof(fmax!float(1.0f, 1.0f))));
    }
}

version (mir_core_test)
@nogc nothrow pure @safe unittest
{
    import mir.math: PI, feqrel;
    assert(feqrel(pow(2.0L, -0.5L), cos(PI / 4)) >= real.mant_dig - 1);
}

version (mir_core_test)
@nogc nothrow pure @safe unittest
{
    import std.meta: AliasSeq;

    static foreach (T; AliasSeq!(float, double, real))
    {{
        // Exercise the CTFE path separately from the runtime implementation.
        enum root = pow(T(4), T(0.5));
        enum reciprocal = powi(T(2), -3);
        static assert(is(typeof(root) == T));
        static assert(is(typeof(reciprocal) == T));
        static assert(root == 2 && reciprocal == T(0.125));
        static assert(powi(T(-1), int.min) == 1);
        static assert(powi(T(-1), int.max) == -1);
        static assert(pow(T(0), T(0)) == 1);
        static assert(powi(T(0), 0) == 1);

        T base = 2;
        assert(pow(base, T(3)) == 8);
        assert(powi(base, -3) == reciprocal);
        assert(pow(T(4), T(0.5)) == root);
        assert(powi(T(-1), int.min) == 1);
        assert(powi(T(-1), 31) == -1);

        // Preserve explicit instantiation and function-address use.
        auto power = &pow!T;
        auto integerPower = &powi!T;
        assert(power(base, T(3)) == 8);
        assert(integerPower(base, -3) == reciprocal);
    }}
}

version (mir_core_test)
@nogc nothrow pure @safe unittest
{
    import std.meta: AliasSeq;
    import std.math: signbit, isNaN;

    // Keep the exponent unknown to the optimizer so these tests exercise
    // runtime intrinsic lowering rather than constant folding.
    pragma(inline, false)
    static T runtimePowi(T)(T base, int exponent)
    {
        return powi(base, exponent);
    }

    static foreach (T; AliasSeq!(float, double, real))
    {{
        static assert(powi(T.nan, 0) == 1);
        static assert(signbit(powi(-T(0), 3)));
        static assert(powi(-T(0), -3) == -T.infinity);
        static assert(signbit(powi(-T.infinity, -3)));

        foreach (exponent; [int.min + 1, -0x1000001, -0xffffff,
                           0xffffff, 0x1000001, int.max])
        {
            assert(runtimePowi(T(-1), exponent) == -1);
            auto zeroPower = runtimePowi(-T(0), exponent);
            auto infinityPower = runtimePowi(-T.infinity, exponent);
            assert(signbit(zeroPower));
            assert(signbit(infinityPower));
            assert(zeroPower == (exponent < 0 ? -T.infinity : -T(0)));
            assert(infinityPower == (exponent < 0 ? -T(0) : -T.infinity));
        }
        foreach (exponent; [int.min, -0x1000000, 0, 0x1000000, int.max - 1])
            assert(runtimePowi(T(-1), exponent) == 1);
        assert(runtimePowi(T.nan, 0) == 1);
        assert(isNaN(runtimePowi(T.nan, 3)));
        assert(runtimePowi(T(2), -3) == T(0.125));
    }}
}

version (mir_core_test)
@nogc nothrow pure @safe unittest
{
    import std.meta: AliasSeq;
    import std.math: signbit, isNaN;

    pragma(inline, false)
    static T runtimePow(T)(T base, T exponent)
    {
        return pow(base, exponent);
    }

    static foreach (T; AliasSeq!(float, double, real))
    {{
        // Explicit expected values: do not use CTFE as the runtime oracle.
        enum T[3][] specialCases = [
            [T(1), T.nan, T(1)],
            [T(1), T.infinity, T(1)],
            [T(1), -T.infinity, T(1)],
            [T(-1), T.infinity, T(1)],
            [T(-1), -T.infinity, T(1)],
            [T.nan, T(0), T(1)],
            [T.nan, T(2), T.nan],
            [T.nan, T.infinity, T.nan],
            [T(2), T.nan, T.nan],
            [-T.infinity, T.nan, T.nan],
            [-T.infinity, -T.infinity, T(0)],
            [-T.infinity, T.infinity, T.infinity],
            [-T.infinity, T(-0.5), T(0)],
            [-T.infinity, T(0.5), T.infinity],
            [-T.infinity, T(-3), -T(0)],
            [-T.infinity, T(3), -T.infinity],
            [-T.infinity, T(-2), T(0)],
            [-T.infinity, T(2), T.infinity],
            [T.infinity, -T.infinity, T(0)],
            [T.infinity, T.infinity, T.infinity],
            [-T(0), T(-3), -T.infinity],
            [-T(0), T(3), -T(0)],
            [-T(0), T(-0.5), T.infinity],
            [-T(0), T(0.5), T(0)],
            [-T(0), T.infinity, T(0)],
            [-T(0), -T.infinity, T.infinity],
            [T(0), T(-3), T.infinity],
            [T(0), T(3), T(0)],
            [T(0.5), T.infinity, T(0)],
            [T(-0.5), -T.infinity, T.infinity],
            [T(-2), T.infinity, T.infinity],
            [T(2), -T.infinity, T(0)],
            [T(-2), T(0.5), T.nan]];

        static foreach (entry; specialCases)
        {{
            enum expected = entry[2];
            enum compileTime = pow(entry[0], entry[1]);
            static if (isNaN(expected))
                static assert(isNaN(compileTime));
            else
                static assert(compileTime == expected
                    && signbit(compileTime) == signbit(expected));

            auto actual = runtimePow(entry[0], entry[1]);
            if (isNaN(expected))
                assert(isNaN(actual));
            else
                assert(actual == expected && signbit(actual) == signbit(expected));
        }}

        static if (T.mant_dig >= 64)
        {
            enum T largeOdd = 0x1p63L + 1;
            static assert(signbit(pow(-T(0), largeOdd)));
            assert(signbit(runtimePow(-T(0), largeOdd)));
            assert(runtimePow(-T.infinity, largeOdd) == -T.infinity);
        }
    }}
}

/// Overload for cdouble, cfloat and creal
@optmath auto fabs(T)(in T x)
    if (isComplex!T)
{
    return x.re * x.re + x.im * x.im;
}

///
version(mir_core_test) unittest
{
    import mir.complex;
    assert(fabs(Complex!double(3, 4)) == 25);
}

/++
Computes whether two values are approximately equal, admitting a maximum
relative difference, and a maximum absolute difference.
Params:
    lhs = First item to compare.
    rhs = Second item to compare.
    maxRelDiff = Maximum allowable difference relative to `rhs`. Defaults to `0.5 ^^ 20`.
    maxAbsDiff = Maximum absolute difference. Defaults to `0.5 ^^ 20`.
        
Returns:
    `true` if the two items are equal or approximately equal under either criterium.
+/
bool approxEqual(T)(const T lhs, const T rhs, const T maxRelDiff = T(0x1p-20f), const T maxAbsDiff = T(0x1p-20f))
    if (isFloatingPoint!T)
{
    if (rhs == lhs) // infs
        return true;
    auto diff = fabs(lhs - rhs);
    if (diff <= maxAbsDiff)
        return true;
    diff /= fabs(rhs);
    return diff <= maxRelDiff;
}

///
@safe pure nothrow @nogc version(mir_core_test) unittest
{
    assert(approxEqual(1.0, 1.0000001));
    assert(approxEqual(1.0f, 1.0000001f));
    assert(approxEqual(1.0L, 1.0000001L));

    assert(approxEqual(10000000.0, 10000001));
    assert(approxEqual(10000000f, 10000001f));
    assert(!approxEqual(100000.0L, 100001L));
}

/// ditto
bool approxEqual(T)(const T lhs, const T rhs, float maxRelDiff = 0x1p-20f, float maxAbsDiff = 0x1p-20f)
    if (isComplexOf!(T, float))
{
    return approxEqual(lhs.re, rhs.re, maxRelDiff, maxAbsDiff)
        && approxEqual(lhs.im, rhs.im, maxRelDiff, maxAbsDiff);
}

deprecated("Use mir.complex.approxEqual instead"):

/// ditto
bool approxEqual(T)(const T lhs, const T rhs, double maxRelDiff = 0x1p-20f, double maxAbsDiff = 0x1p-20f)
    if (isComplexOf!(T, double))
{
    return approxEqual(lhs.re, rhs.re, maxRelDiff, maxAbsDiff)
        && approxEqual(lhs.im, rhs.im, maxRelDiff, maxAbsDiff);
}

/// ditto
bool approxEqual(T)(const T lhs, const T rhs, real maxRelDiff = 0x1p-20f, real maxAbsDiff = 0x1p-20f)
    if (isComplexOf!(T, real))
{
    return approxEqual(lhs.re, rhs.re, maxRelDiff, maxAbsDiff)
        && approxEqual(lhs.im, rhs.im, maxRelDiff, maxAbsDiff);
}

/// Complex types works as `approxEqual(l.re, r.re) && approxEqual(l.im, r.im)`
@safe pure nothrow @nogc version(mir_core_test) unittest
{
    import mir.internal.utility: isComplexOf;
    static struct UserComplex(T) { T re, im; }
    alias _cdouble = UserComplex!double;

    static assert(isComplexOf!(_cdouble, double));

    assert(approxEqual(_cdouble(1.0, 1), _cdouble(1.0000001, 1), 1.0000001));
    assert(!approxEqual(_cdouble(100000.0L, 0), _cdouble(100001L, 0)));
}
