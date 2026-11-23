
/++
Complex math

Copyright: Ilia Ki; 2010, Lars T. Kyllingstad (original Phobos code)
Authors: Ilia Ki, Lars Tandle Kyllingstad, Don Clugston
+/
module mir.complex.math;

public import mir.complex;

/++
Params: z = A complex number.
Returns: The square root of `z`.
+/
Complex!T sqrt(T)(Complex!T z)  @safe pure nothrow @nogc
{
    import mir.math.common: fabs, fmin, fmax, sqrt;

    if (z == 0)
        return typeof(return)(0, 0);
    auto x = fabs(z.re);
    auto y = fabs(z.im);
    auto n = fmin(x, y);
    auto m = fmax(x, y);
    auto r = n / m;
    auto w = sqrt(m) * sqrt(0.5f * ((x >= y ? 1 : r) + sqrt(1 + r * r)));
    auto s = typeof(return)(w, z.im / (w + w));
    if (z.re < 0)
    {
        s = typeof(return)(s.im, s.re);
        if (z.im < 0)
            s = -s;
    }
    return s;
}

///
@safe pure nothrow unittest
{
    assert(sqrt(complex(0.0)) == 0.0);
    assert(sqrt(complex(1.0, 0)) == 1.0);
    assert(sqrt(complex(-1.0, 0)) == complex(0, 1.0));
    assert(sqrt(complex(-8.0, -6.0)) == complex(1.0, -3.0));
}

@safe pure nothrow unittest
{
    assert(complex(1.0, 1.0).sqrt.approxEqual(complex(1.098684113467809966, 0.455089860562227341)));
    assert(complex(0.5, 2.0).sqrt.approxEqual(complex(1.131713924277869410, 0.883615530875513265)));
}

/**
 * Calculate the natural logarithm of x.
 * The branch cut is along the negative axis.
 * Params:
 *      x = A complex number
 * Returns:
 *      The complex natural logarithm of `x`
 *
 *      $(TABLE_SV
 *      $(TR $(TH x)                           $(TH log(x)))
 *      $(TR $(TD (-0, +0))                    $(TD (-$(INFIN), $(PI))))
 *      $(TR $(TD (+0, +0))                    $(TD (-$(INFIN), +0)))
 *      $(TR $(TD (any, +$(INFIN)))            $(TD (+$(INFIN), $(PI)/2)))
 *      $(TR $(TD (any, $(NAN)))               $(TD ($(NAN), $(NAN))))
 *      $(TR $(TD (-$(INFIN), any))            $(TD (+$(INFIN), $(PI))))
 *      $(TR $(TD (+$(INFIN), any))            $(TD (+$(INFIN), +0)))
 *      $(TR $(TD (-$(INFIN), +$(INFIN)))      $(TD (+$(INFIN), 3$(PI)/4)))
 *      $(TR $(TD (+$(INFIN), +$(INFIN)))      $(TD (+$(INFIN), $(PI)/4)))
 *      $(TR $(TD ($(PLUSMN)$(INFIN), $(NAN))) $(TD (+$(INFIN), $(NAN))))
 *      $(TR $(TD ($(NAN), any))               $(TD ($(NAN), $(NAN))))
 *      $(TR $(TD ($(NAN), +$(INFIN)))         $(TD (+$(INFIN), $(NAN))))
 *      $(TR $(TD ($(NAN), $(NAN)))            $(TD ($(NAN), $(NAN))))
 *      )
 */
Complex!T log(T)(Complex!T x) @safe pure nothrow @nogc
{
    import mir.math.constant: PI, PI_4, PI_2;
    import mir.math.common: log, fabs, copysign;
    alias isNaN = x => x != x;
    alias isInfinity = x => x.fabs == T.infinity;

    // Handle special cases explicitly here for better accuracy.
    // The order here is important, so that the correct path is chosen.
    if (isNaN(x.re))
    {
        if (isInfinity(x.im))
            return Complex!T(T.infinity, T.nan);
        else
            return Complex!T(T.nan, T.nan);
    }
    if (isInfinity(x.re))
    {
        if (isNaN(x.im))
            return Complex!T(T.infinity, T.nan);
        else if (isInfinity(x.im))
        {
            if (copysign(1, x.re) < 0)
                return Complex!T(T.infinity, copysign(3.0 * PI_4, x.im));
            else
                return Complex!T(T.infinity, copysign(PI_4, x.im));
        }
        else
        {
            if (copysign(1, x.re) < 0)
                return Complex!T(T.infinity, copysign(PI, x.im));
            else
                return Complex!T(T.infinity, copysign(0.0, x.im));
        }
    }
    if (isNaN(x.im))
        return Complex!T(T.nan, T.nan);
    if (isInfinity(x.im))
        return Complex!T(T.infinity, copysign(PI_2, x.im));
    if (x.re == 0.0 && x.im == 0.0)
    {
        if (copysign(1, x.re) < 0)
            return Complex!T(-T.infinity, copysign(PI, x.im));
        else
            return Complex!T(-T.infinity, copysign(0.0, x.im));
    }

    T logOnePlus(T value) @safe pure nothrow @nogc
    {
        import std.math.exponential: log1p;
        if (__ctfe)
        {
            // log1p uses runtime intrinsics on some compilers. Here value is
            // in [-0.75, 3.5], so the atanh series converges geometrically.
            auto y = value / (2 + value);
            auto square = y * y;
            auto term = y;
            auto sum = y;
            foreach (i; 1 .. 2 * T.mant_dig)
            {
                term *= square;
                auto next = sum + term / (2 * i + 1);
                if (next == sum)
                    break;
                sum = next;
            }
            return 2 * sum;
        }
        return log1p(value);
    }

    auto a = fabs(x.re);
    auto b = fabs(x.im);
    auto large = a >= b ? a : b;
    auto small = a >= b ? b : a;
    T logMagnitude;
    if (large >= T(0.5) && large <= T(1.5))
    {
        // Recover the rounding errors of the squares before subtracting one.
        // Near the unit circle those errors can determine the result's sign.
        real squareError(real v, real square) @safe pure nothrow @nogc
        {
            int precision = real.mant_dig;
            if (__ctfe)
            {
                // CTFE can evaluate real with more precision than the target.
                precision = 1;
                real probe = 1;
                while (1 + probe / 2 != 1)
                {
                    probe /= 2;
                    ++precision;
                }
            }
            real splitter = (1UL << ((precision + 1) / 2)) + 1.0L;
            auto split = splitter * v;
            auto high = split - (split - v);
            auto low = v - high;
            return ((high * high - square) + 2 * high * low) + low * low;
        }
        real sumError(real a, real b, real sum) @safe pure nothrow @nogc
        {
            auto part = sum - a;
            return (a - (sum - part)) + (b - part);
        }
        real u = large, v = small;
        auto uu = u * u;
        auto vv = v * v;
        auto difference = uu - 1;
        auto sum = difference + vv;
        auto correction = squareError(u, uu) + squareError(v, vv)
            + sumError(uu, -1, difference) + sumError(difference, vv, sum);
        T delta = cast(T) (sum + correction);
        logMagnitude = T(0.5) * logOnePlus(delta);
    }
    else
    {
        // The magnitude itself may overflow or round a subnormal input.
        auto ratio = small / large;
        logMagnitude = log(large) + T(0.5) * logOnePlus(ratio * ratio);
    }
    return Complex!T(logMagnitude, arg(x));
}

@safe pure nothrow @nogc version(mir_core_test) unittest
{
    import mir.math.common: scalarLog = log, fabs;
    import mir.math.constant: LN2, PI_4;
    import std.meta: AliasSeq;

    bool check(T)() @safe pure nothrow @nogc
    {
        // Scalar log may have only double precision during CTFE.
        auto scalarEpsilon = __ctfe && T.mant_dig > double.mant_dig
            ? T(double.epsilon) : T.epsilon;
        foreach (v; [T.max, T.min_normal, T.min_normal * T.epsilon])
        {
            // The scalar log CTFE implementation may narrow real to double.
            if (__ctfe && T.mant_dig > double.mant_dig)
                continue;
            auto result = log(Complex!T(v, v));
            auto expected = scalarLog(v) + T(LN2 / 2);
            assert(fabs(result.re - expected) <= 8 * T.epsilon * fabs(expected));
            assert(fabs(result.im - T(PI_4)) <= 8 * T.epsilon);
        }

        // The magnitude rounds to one, but its logarithm is representable.
        foreach (s; [T(-1), T(1)])
        {
            auto result = log(Complex!T(s, T(0x1p-30L)));
            enum T expected = 0x1p-61L - 0x1p-122L;
            assert(fabs(result.re - expected) <= 8 * T.epsilon * expected);
            auto swapped = log(Complex!T(T(0x1p-30L), s));
            assert(swapped.re == result.re);
        }

        // References use the exact binary inputs, not their decimal spellings.
        static if (T.mant_dig == float.mant_dig)
        {
            enum T cancellationReal = 0x1.d54178p-1;
            enum T cancellationImag = 0x1.99999ap-2;
            enum T cancellationExpected = -2.24240004930311885077424941924e-8L;
        }
        else
        {
            enum T cancellationReal = 0x1.d54178e8830d5p-1L;
            enum T cancellationImag = 0x1.999999999999ap-2L;
            enum T cancellationExpected = -3.32132266633030497888746895455691260915599065e-18L;
        }
        foreach (reSign; [T(-1), T(1)])
        foreach (imSign; [T(-1), T(1)])
        {
            auto result = log(Complex!T(reSign * cancellationReal, imSign * cancellationImag));
            assert(fabs(result.re - cancellationExpected)
                <= 32 * T.epsilon * fabs(cancellationExpected));
            assert(log(Complex!T(imSign * cancellationImag, reSign * cancellationReal)).re
                == result.re);
        }

        foreach (base; [T(0.5), T(1), T(1.5)])
        {
            T logBase = base == T(0.5) ? -T(LN2)
                : base == 1 ? T(0) : T(0.405465108108164381978013115464349137L);
            auto diagonal = log(Complex!T(base, base));
            assert(fabs(diagonal.re - (logBase + T(LN2 / 2))) <= 8 * T.epsilon);
            foreach (offset; [-T.epsilon, T(0), T.epsilon])
            {
                auto result = log(Complex!T(base + offset, 0));
                T expected = logBase + offset / base;
                assert(fabs(result.re - expected) <= 16 * scalarEpsilon * fabs(expected));
            }
        }
        auto ordinary = log(Complex!T(3, 4));
        assert(fabs(ordinary.re - T(1.60943791243410037460075933322618764L))
            <= 8 * scalarEpsilon);
        return true;
    }

    static foreach (T; AliasSeq!(float, double, real))
    {
        static assert(check!T());
        assert(check!T());
    }
}

///
@safe pure nothrow @nogc version(mir_core_test) unittest
{
    import mir.math.common: sqrt;
    import mir.math.constant: PI;
    import mir.math.common: approxEqual;

    auto a = complex(2.0, 1.0);
    assert(log(conj(a)) == conj(log(a)));

    assert(log(complex(-1.0L, 0.0L)) == complex(0.0L, PI));
    assert(log(complex(-1.0L, -0.0L)) == complex(0.0L, -PI));
}

@safe pure nothrow @nogc version(mir_core_test) unittest
{
    import mir.math.common: fabs;
    import mir.math.constant: PI, PI_2, PI_4;
    alias isNaN = x => x != x;
    alias isInfinity = x => x.fabs == x.infinity;

    auto a = log(complex(-0.0L, 0.0L));
    assert(a == complex(-real.infinity, PI));
    auto b = log(complex(0.0L, 0.0L));
    assert(b == complex(-real.infinity, +0.0L));
    auto c = log(complex(1.0L, real.infinity));
    assert(c == complex(real.infinity, PI_2));
    auto d = log(complex(1.0L, real.nan));
    assert(isNaN(d.re) && isNaN(d.im));

    auto e = log(complex(-real.infinity, 1.0L));
    assert(e == complex(real.infinity, PI));
    auto f = log(complex(real.infinity, 1.0L));
    assert(f == complex(real.infinity, 0.0L));
    auto g = log(complex(-real.infinity, real.infinity));
    assert(g == complex(real.infinity, 3.0 * PI_4));
    auto h = log(complex(real.infinity, real.infinity));
    assert(h == complex(real.infinity, PI_4));
    auto i = log(complex(real.infinity, real.nan));
    assert(isInfinity(i.re) && isNaN(i.im));

    auto j = log(complex(real.nan, 1.0L));
    assert(isNaN(j.re) && isNaN(j.im));
    auto k = log(complex(real.nan, real.infinity));
    assert(isInfinity(k.re) && isNaN(k.im));
    auto l = log(complex(real.nan, real.nan));
    assert(isNaN(l.re) && isNaN(l.im));
}

@safe pure nothrow @nogc version(mir_core_test) unittest
{
    import mir.math.constant: PI;

    auto a = log(fromPolar(1.0, PI / 6.0));
    assert(approxEqual(a, complex(0.0L, 0.523598775598298873077L), 0.0, 1e-15));

    auto b = log(fromPolar(1.0, PI / 3.0));
    assert(approxEqual(b, complex(0.0L, 1.04719755119659774615L), 0.0, 1e-15));

    auto c = log(fromPolar(1.0, PI / 2.0));
    assert(approxEqual(c, complex(0.0L, 1.57079632679489661923L), 0.0, 1e-15));

    auto d = log(fromPolar(1.0, 2.0 * PI / 3.0));
    assert(approxEqual(d, complex(0.0L, 2.09439510239319549230L), 0.0, 1e-15));

    auto e = log(fromPolar(1.0, 5.0 * PI / 6.0));
    assert(approxEqual(e, complex(0.0L, 2.61799387799149436538L), 0.0, 1e-15));

    auto f = log(complex(-1.0L, 0.0L));
    assert(approxEqual(f, complex(0.0L, PI), 0.0, 1e-15));
}

/++
Calculates e$(SUPERSCRIPT x).
Params:
     x = A complex number
Returns:
     The complex base e exponential of `x`
     $(TABLE_SV
     $(TR $(TH x)                           $(TH exp(x)))
     $(TR $(TD ($(PLUSMN)0, +0))            $(TD (1, +0)))
     $(TR $(TD (any, +$(INFIN)))            $(TD ($(NAN), $(NAN))))
     $(TR $(TD (any, $(NAN))                $(TD ($(NAN), $(NAN)))))
     $(TR $(TD (+$(INFIN), +0))             $(TD (+$(INFIN), +0)))
     $(TR $(TD (-$(INFIN), any))            $(TD ($(PLUSMN)0, cis(x.im))))
     $(TR $(TD (+$(INFIN), any))            $(TD ($(PLUSMN)$(INFIN), cis(x.im))))
     $(TR $(TD (-$(INFIN), +$(INFIN)))      $(TD ($(PLUSMN)0, $(PLUSMN)0)))
     $(TR $(TD (+$(INFIN), +$(INFIN)))      $(TD ($(PLUSMN)$(INFIN), $(NAN))))
     $(TR $(TD (-$(INFIN), $(NAN)))         $(TD ($(PLUSMN)0, $(PLUSMN)0)))
     $(TR $(TD (+$(INFIN), $(NAN)))         $(TD ($(PLUSMN)$(INFIN), $(NAN))))
     $(TR $(TD ($(NAN), +0))                $(TD ($(NAN), +0)))
     $(TR $(TD ($(NAN), any))               $(TD ($(NAN), $(NAN))))
     $(TR $(TD ($(NAN), $(NAN)))            $(TD ($(NAN), $(NAN))))
     )
+/
Complex!T exp(T)(Complex!T x) @trusted pure nothrow @nogc // TODO: @safe
{
    import mir.math.common: exp, fabs, copysign;
    alias isNaN = x => x != x;
    alias isInfinity = x => x.fabs == T.infinity;

    // Preserve the imaginary zero, even when the real exponential overflows.
    if (x.im == 0)
        return Complex!T(exp(x.re), x.im);

    // Handle special cases explicitly here, as fromPolar will otherwise
    // cause them to return Complex!T(NaN, NaN), or with the wrong sign.
    if (isInfinity(x.re))
    {
        if (isNaN(x.im))
        {
            if (copysign(1, x.re) < 0)
                return Complex!T(0, copysign(0, x.im));
            else
                return x;
        }
        if (isInfinity(x.im))
        {
            if (copysign(1, x.re) < 0)
                return Complex!T(0, copysign(0, x.im));
            else
                return Complex!T(T.infinity, -T.nan);
        }
    }
    if (isNaN(x.re))
    {
        if (isNaN(x.im) || isInfinity(x.im))
            return Complex!T(T.nan, T.nan);
    }
    if (x.re == 0)
    {
        if (isNaN(x.im) || isInfinity(x.im))
            return Complex!T(T.nan, T.nan);
    }

    return fromPolar!T(exp(x.re), x.im);
}

@safe pure nothrow @nogc version(mir_core_test) unittest
{
    import mir.math.ieee: signbit;
    import std.meta: AliasSeq;

    static foreach (T; AliasSeq!(float, double, real))
    {
        static assert(is(typeof(exp(Complex!T(0, 0))) == Complex!T));
    }

    bool check(T)() @safe pure nothrow @nogc
    {
        foreach (im; [T(0.0), -T(0.0)])
        {
            foreach (re; [T(0.0), -T(0.0), T.infinity, -T.infinity,
                          T.max, -T.max, T.nan])
            {
                auto result = exp(Complex!T(re, im));
                assert(result.im == 0 && signbit(result.im) == signbit(im));
                if (re != re)
                    assert(result.re != result.re);
                else if (re == 0)
                    assert(result.re == 1);
                else if (re > 0)
                    assert(result.re == T.infinity);
                else
                    assert(result.re == 0 && !signbit(result.re));
            }
        }
        return true;
    }

    static foreach (T; AliasSeq!(float, double, real))
    {
        static assert(check!T());
        assert(check!T());
    }
}

///
@safe pure nothrow @nogc version(mir_core_test) unittest
{
    import mir.math.constant: PI;

    assert(exp(complex(0.0, 0.0)) == complex(1.0, 0.0));

    auto a = complex(2.0, 1.0);
    assert(exp(conj(a)) == conj(exp(a)));

    auto b = exp(complex(0.0, 1.0) * double(PI));
    assert(approxEqual(b, complex(-1.0), 0.0, 1e-15));
}

@safe pure nothrow @nogc version(mir_core_test) unittest
{
    import mir.math.common: fabs;

    alias isNaN = x => x != x;
    alias isInfinity = x => x.fabs == x.infinity;

    auto a = exp(complex(0.0, double.infinity));
    assert(isNaN(a.re) && isNaN(a.im));
    auto b = exp(complex(0.0, double.infinity));
    assert(isNaN(b.re) && isNaN(b.im));
    auto c = exp(complex(0.0, double.nan));
    assert(isNaN(c.re) && isNaN(c.im));

    auto d = exp(complex(+double.infinity, 0.0));
    assert(d == complex(double.infinity, 0.0));
    auto e = exp(complex(-double.infinity, 0.0));
    assert(e == complex(0.0));
    auto f = exp(complex(-double.infinity, 1.0));
    assert(f == complex(0.0));
    auto g = exp(complex(+double.infinity, 1.0));
    assert(g == complex(double.infinity, double.infinity));
    auto h = exp(complex(-double.infinity, +double.infinity));
    assert(h == complex(0.0));
    auto i = exp(complex(+double.infinity, +double.infinity));
    assert(isInfinity(i.re) && isNaN(i.im));
    auto j = exp(complex(-double.infinity, double.nan));
    assert(j == complex(0.0));
    auto k = exp(complex(+double.infinity, double.nan));
    assert(isInfinity(k.re) && isNaN(k.im));

    auto l = exp(complex(double.nan, 0));
    assert(isNaN(l.re) && l.im == 0.0);
    auto m = exp(complex(double.nan, 1));
    assert(isNaN(m.re) && isNaN(m.im));
    auto n = exp(complex(double.nan, double.nan));
    assert(isNaN(n.re) && isNaN(n.im));
}

@safe pure nothrow @nogc version(mir_core_test) unittest
{
    import mir.math.constant : PI;

    auto a = exp(complex(0.0, -PI));
    assert(approxEqual(a, complex(-1.0L), 0.0, 1e-15));

    auto b = exp(complex(0.0, -2.0 * PI / 3.0));
    assert(approxEqual(b, complex(-0.5L, -0.866025403784438646763L)));

    auto c = exp(complex(0.0, PI / 3.0));
    assert(approxEqual(c, complex(0.5L, 0.866025403784438646763L)));

    auto d = exp(complex(0.0, 2.0 * PI / 3.0));
    assert(approxEqual(d, complex(-0.5L, 0.866025403784438646763L)));

    auto e = exp(complex(0.0, PI));
    assert(approxEqual(e, complex(-1.0L), 0.0, 1e-15));
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
bool approxEqual(T)(Complex!T lhs, Complex!T rhs, const T maxRelDiff = 0x1p-20f, const T maxAbsDiff = 0x1p-20f)
{
    import mir.math.common: approxEqual;
    return approxEqual(lhs.re, rhs.re, maxRelDiff, maxAbsDiff)
        && approxEqual(lhs.im, rhs.im, maxRelDiff, maxAbsDiff);
}

/// Complex types works as `approxEqual(l.re, r.re) && approxEqual(l.im, r.im)`
@safe pure nothrow @nogc version(mir_core_test) unittest
{
    assert(approxEqual(complex(1.0, 1), complex(1.0000001, 1), 1.0000001));
    assert(!approxEqual(complex(100000.0, 0), complex(100001.0, 0)));
}
