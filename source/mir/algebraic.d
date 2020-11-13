/++
This module implements a generic variant and nullable types.
+/
module mir.algebraic;

import mir.functional: naryFun;
import std.meta: allSatisfy;

private static immutable variantExceptionMsg = "mir.variant: the variant stores other type then requested.";
private static immutable variantNullExceptionMsg = "mir.variant: the variant is empty and doesn't store any value.";
private static immutable variantMemberExceptionMsg = "mir.variant: the variant is stores the type that isn't compatible with the user provided visitor and arguments.";

version (D_Exceptions)
{
    private static immutable variantException = new Exception(variantExceptionMsg);
    private static immutable variantNullException = new Exception(variantNullExceptionMsg);
    private static immutable variantMemberException = new Exception(variantMemberExceptionMsg);
}

private alias ConstOf(T) = const T;
private enum Alignof(T) = T.alignof;
private enum canConstructWith(From, To) = __traits(compiles, (From a) { To b = a; } );
private enum canImplicitlyRemoveConst(T) = __traits(compiles, {static T _function_(ref const T a) { return a; }} );
private enum canRemoveConst(T) = canConstructWith!(const T, T);
private enum canRemoveImmutable(T) = canConstructWith!(immutable T, T);
private enum hasOpPostMove(T) = __traits(hasMember, T, "opPostMove");
private enum hasToHash(T) = __traits(hasMember, T, "toHash");
private enum isCopyable(S) = __traits(isCopyable, S); 
private enum isPOD(T) = __traits(isPOD, T);
private enum isVariant(T) = __traits(hasMember, T, "_isVariant");
private enum Sizeof(T) = T.sizeof;

private enum hasInoutConstruction(T) = __traits(compiles, {static struct S { T a; this(ref return scope inout S rhs) inout { this.a = rhs.a; } }} );
private enum hasConstConstruction(T) = __traits(compiles, {static struct S { T a; this(ref return scope const S rhs) const { this.a = rhs.a; } }} );
private enum hasImmutableConstruction(T) = __traits(compiles, {static struct S { T a; this(ref return scope immutable S rhs) immutable { this.a = rhs.a; } }} );
private enum hasMutableConstruction(T) = __traits(compiles, {static struct S { T a; this(ref return scope S rhs) { this.a = rhs.a; } }} );
private enum hasSemiImmutableConstruction(T) = __traits(compiles, {static struct S { T a; this(ref return scope const S rhs) immutable { this.a = rhs.a; } }} );
private enum hasSemiMutableConstruction(T) = __traits(compiles, {static struct S { T a; this(ref return scope const S rhs) { this.a = rhs.a; } }} );

@safe version(mir_core_test) unittest
{
    static struct S { this(ref return scope inout S) inout {} }
    static inout(S) _function_(ref inout S a) { return S(a); }
    static struct C2 { uint* a; this(ref return scope const S) const {} }
    static assert(hasInoutConstruction!uint);
    static assert(hasInoutConstruction!(immutable(uint)[]));
    static assert(hasInoutConstruction!(typeof(null)));
    static assert(hasInoutConstruction!S);
}

private template staticIsSorted(alias cmp, Seq...)
{
    static if (Seq.length <= 1)
        enum staticIsSorted = true;
    else static if (Seq.length == 2)
        enum staticIsSorted = cmp!(Seq[0], Seq[1]);
    else
    {
        enum staticIsSorted =
            cmp!(Seq[($ / 2) - 1], Seq[$ / 2]) &&
            staticIsSorted!(cmp, Seq[0 .. $ / 2]) &&
            staticIsSorted!(cmp, Seq[$ / 2 .. $]);
    }
}

private template TryRemoveConst(T)
{
    import std.traits: Unqual;
    alias U = Unqual!T;
    static if (canImplicitlyRemoveConst!U)
    {
        alias TryRemoveConst = U;
    }
    else
    {
        alias TryRemoveConst = T;
    }
}

version(mir_core_test) unittest
{
    static assert(is(TryRemoveConst!(const int) == int));
}

private template TypeCmp(A, B)
{
    enum bool TypeCmp = is(A == B) ? false:
    is(A == typeof(null)) ? true:
    is(B == typeof(null)) ? false:
    is(A == void) ? true:
    is(B == void) ? false:
    A.sizeof < B.sizeof ? true:
    A.sizeof > B.sizeof ? false:
    A.mangleof < B.mangleof;
}

private template isInstanceOf(alias S)
{
    enum isInstanceOf(T) = is(T == S!Args, Args...);
}

private struct VariantSet(Sets...);

/++
Dummy type for $(LREF Variant) self-referencing.
+/
struct SetAlias(uint id) {}
///ditto
struct This {}

/++
+/
template TypeSet(T...)
{
    import std.meta: NoDuplicates, staticSort, staticMap;
    // sort types by siezeof and them mangleof
    // but typeof(null) goes first
    static if (is(staticMap!(TryRemoveConst, T) == T))
        static if (is(NoDuplicates!T == T))
            static if (staticIsSorted!(TypeCmp, T))
                struct TypeSet;
            else
                alias TypeSet = .TypeSet!(staticSort!(TypeCmp, T));
        else
            alias TypeSet = TypeSet!(NoDuplicates!T);
    else
        alias TypeSet = staticMap!(TryRemoveConst, T);
}


version(mir_core_test) unittest
{
    struct S {}
    alias C = S;
    alias Int = int;
    static assert(__traits(isSame, TypeSet!(S, int), TypeSet!(Int, C)));
    static assert(__traits(isSame, TypeSet!(S, int, int), TypeSet!(Int, C)));
    static assert(!__traits(isSame, TypeSet!(uint, S), TypeSet!(int, S)));
}


/++
$(H4 Cyclic-Referential Types)
A useful and popular use of algebraic data structures is for defining cyclic
$(LUCKY self-referential data structures), i.e. a kit of structures that embed references to
values of their own type within.
This is achieved with $(LREF Variants) by using $(LREF SetAlias) as a placeholder whenever a
reference to the type being defined is needed. The $(LREF Variant) instantiation
will perform $(LINK2 https://en.wikipedia.org/wiki/Name_resolution_(programming_languages)#Alpha_renaming_to_make_name_resolution_trivial,
alpha renaming) on its constituent types, replacing $(LREF SetAlias)
with the self-referenced type. The structure of the type involving $(LREF SetAlias) may
be arbitrarily complex.
+/
template Variants(Sets...)
    if (allSatisfy!(isInstanceOf!TypeSet, Sets))
{
    import std.meta: staticMap;
    import mir.internal.utility: Iota;

    private alias TypeSetsInst(uint id) = Algebraic!(id, Sets);
    ///
    alias Variants = staticMap!(TypeSetsInst, Iota!(Sets.length));
}

/// 
@safe pure nothrow version(mir_core_test) unittest
{
    import std.meta: AliasSeq;

    alias V = Variants!(
        TypeSet!(string, long, SetAlias!1*), // string, long, and V[1]*
        TypeSet!(SetAlias!0[], int), // int and V[0]*
    );

    alias A = V[0];
    alias B = V[1];

    A arr = new B([A("hey"), A(100)]);
    assert(arr._is!(B*));
    assert(arr.trustedGet!(B*)._is!(A[]));
}

private static struct _Null()
{
@safe pure nothrow @nogc const:
    size_t toHash() {return 0;}
    bool opEquals(_Null) { return true; }
    int opCmp(_Null) { return 0; }
    typeof(null) __self() @property { return null; }
    typeof(null) __self(typeof(null)) @property { return null; }
    this(typeof(null)) inout {}
    string toString() { return "null"; }
}

private static struct _Void()
{
 @safe pure nothrow @nogc const:
    size_t toHash() {return 0;}
    bool opEquals(_Void) { return true; }
    int opCmp(_Void) { return 0; }
    void __self() @property { return; }
    string toString() { return "void"; }
}

/++
Implementation of $(LREF Variant), $(LREF Variants), and $(LREF Nullable).
+/
struct Algebraic(uint _setId, _TypeSets...)
    if (allSatisfy!(isInstanceOf!TypeSet, _TypeSets))
{
    private enum _isVariant;

    import core.lifetime: moveEmplace;
    import mir.conv: emplaceRef;
    import std.meta: AliasSeq, anySatisfy, allSatisfy, staticMap, templateOr, Replace;
    import std.traits:
        hasElaborateAssign,
        hasElaborateCopyConstructor,
        hasElaborateDestructor,
        isEqualityComparable,
        isOrderingComparable,
        Largest,
        TemplateArgsOf,
        Unqual
        ;

    private template _ApplyAliasesImpl(int length, Types...)
    {
        import std.typecons: ReplaceTypeUnless;
        static if (length == 0)
            alias _ApplyAliasesImpl = ReplaceTypeUnless!(isVariant, This, Algebraic!(_setId, _TypeSets), Types);
        else
        {
            enum next  = length - 1;
            alias _ApplyAliasesImpl = _ApplyAliasesImpl!(next,
                ReplaceTypeUnless!(isVariant, SetAlias!next, Algebraic!(next, _TypeSets), Types));
        }
    }

    ///
    alias AllowedTypes = AliasSeq!(_ApplyAliasesImpl!(_TypeSets.length, TemplateArgsOf!(_TypeSets[_setId])));

    private alias _Payload = Replace!(void, _Void!(), Replace!(typeof(null), _Null!(), AllowedTypes));

    private static union _Storage
    {
        _Payload payload;

        static if (AllowedTypes.length == 0 || is(AllowedTypes == AliasSeq!(typeof(null))))
        {
            ubyte[0] bytes;
            static if (AllowedTypes.length)
                enum uint id = 0;
        }
        else
        struct
        {
            ubyte[Largest!_Payload.sizeof] bytes;

            static if (AllowedTypes.length > 1)
            {
                import mir.utility: max;
                enum _alignof = max(staticMap!(Alignof, _Payload));
                static if ((bytes.length | _alignof) & 1)
                    ubyte id;
                else
                static if ((bytes.length | _alignof) & 2)
                    ushort id;
                else
                    uint id;
            }
            else
            {
                enum uint id = 0;
            }
        }
    
        static if (bytes.length && AllowedTypes.length)
            ubyte[bytes.length + id.sizeof] allBytes;
        else
            alias allBytes = bytes;
    }

    private _Storage _storage;

    static if (anySatisfy!(hasElaborateDestructor, AllowedTypes))
    ~this() @safe
    {
        S: switch (_storage.id)
        {
            static foreach (i, T; AllowedTypes)
            static if (hasElaborateDestructor!T)
            {
                case i:
                    _mutableTrustedGet!T.__xdtor;
                    break S;
            }
            default:
        }
        version(mir_secure_memory)
            _storage.allBytes = 0xCC;
    }

    static if (anySatisfy!(hasOpPostMove, AllowedTypes))
    void opPostMove(const ref typeof(this) old)
    {
        S: switch (_storage.id)
        {
            static foreach (i, T; AllowedTypes)
            static if (hasOpPostMove!T)
            {
                case i:
                    this._storage.payload[i].opPostMove(old._storage.payload[i]);
                    return;
            }
            default: return;
        }
    }

    static if (AllowedTypes.length)
    {
        static if (!__traits(compiles, (){ AllowedTypes[0] arg; }))
        {
            @disable this();
        }
    }

    private ref trustedBytes() inout @trusted
    {
        return *cast(ubyte[_storage.bytes.length]*)&this._storage.bytes;
    }

    static if (!allSatisfy!(isCopyable, AllowedTypes))
        @disable this(this);
    else
    static if (anySatisfy!(hasElaborateCopyConstructor, AllowedTypes))
    {
        // private enum _allCanImplicitlyRemoveConst = allSatisfy!(canImplicitlyRemoveConst, AllowedTypes);
        // private enum _allCanRemoveConst = allSatisfy!(canRemoveConst, AllowedTypes);
        // private enum _allHaveImplicitSemiMutableConstruction = _allCanImplicitlyRemoveConst && _allHaveMutableConstruction;

        private static union _StorageI(uint i)
        {
            _Payload[i] payload;
            ubyte[_Payload[i].sizeof] bytes;
        }

        private void _copyCtorSwitch(this This, RhsAlgebraic)(return ref scope RhsAlgebraic rhs)
        {
            switch (_storage.id)
            {
                static foreach (i, T; AllowedTypes)
                static if (!is(T == typeof(null)) && !is(T == void) && hasElaborateCopyConstructor!T)
                {
                    case i: {
                        import std.traits: CopyTypeQualifiers;
                        CopyTypeQualifiers!(RhsAlgebraic, _StorageI!i) storage = { rhs._storage.payload[i] };
                        trustedBytes[0 .. storage.bytes.length] = storage.bytes;
                        return;
                    }
                }
                default: return;
            }
        }

        static if (allSatisfy!(hasInoutConstruction, AllowedTypes))
        this(return ref scope inout Algebraic rhs) inout
        {
            this._storage.allBytes = rhs._storage.allBytes;
            _copyCtorSwitch(rhs);
        }
        else
        {
            static if (allSatisfy!(hasMutableConstruction, AllowedTypes))
            this(return ref scope Algebraic rhs)
            {
                this._storage.allBytes = rhs._storage.allBytes;
                _copyCtorSwitch(rhs);
            }

            static if (allSatisfy!(hasConstConstruction, AllowedTypes))
            this(return ref scope const Algebraic rhs) const
            {
                this._storage.allBytes = rhs._storage.allBytes;
                _copyCtorSwitch(rhs);
            }

            static if (allSatisfy!(hasImmutableConstruction, AllowedTypes))
            this(return ref scope immutable Algebraic rhs) immutable
            {
                this._storage.allBytes = rhs._storage.allBytes;
                _copyCtorSwitch(rhs);
            }

            static if (allSatisfy!(hasSemiImmutableConstruction, AllowedTypes))
            this(return ref scope const Algebraic rhs) immutable
            {
                this._storage.allBytes = rhs._storage.allBytes;
                _copyCtorSwitch(rhs);
            }

            static if (allSatisfy!(hasSemiMutableConstruction, AllowedTypes))
            this(return ref scope const Algebraic rhs)
            {
                this._storage.allBytes = rhs._storage.allBytes;
                _copyCtorSwitch(rhs);
            }
        }
    }

    /++
    +/
    size_t toHash() const
    {
        static if (allSatisfy!(isPOD, AllowedTypes))
        {
            static if (AllowedTypes.length == 0 || is(AllowedTypes == AliasSeq!(typeof(null))))
            {
                return 0;
            }
            else
            static if (this.sizeof <= 16)
            {
                return hashOf(_storage.bytes, _storage.id);
            }
            else
            {
                static if (this.sizeof <= ubyte.max)
                    alias UInt = ubyte;
                else
                static if (this.sizeof <= ushort.max)
                    alias UInt = ushort;
                else
                    alias UInt = uint;

                static immutable UInt[_Payload.length + 1] sizes = [0, staticMap!(Sizeof, _Payload)];
                return hashOf(_storage.bytes[0 .. sizes[_storage.id]], _storage.id);
            }
        }
        else
        switch (_storage.id)
        {
            static foreach (i, T; AllowedTypes)
            {
                case i:
                    return hashOf(_storage.payload[i], i);
            }
            default: assert(0);
        }
    }

    /++
    +/
    bool opEquals()(auto ref const typeof(this) rhs) const
    {
        static if (AllowedTypes.length == 0)
        {
            return true;
        }
        else
        {
            if (this._storage.id != rhs._storage.id)
                return false;
            switch (_storage.id)
            {
                static foreach (i, T; AllowedTypes)
                {
                    case i:
                        return this.trustedGet!T == rhs.trustedGet!T;
                }
                default: assert(0);
            }
        }
    }

    /++
    +/
    auto opCmp()(auto ref const typeof(this) rhs) const
    {
        static if (AllowedTypes.length == 0)
        {
            return 0;
        }
        else
        {
            import mir.internal.utility: isFloatingPoint;
            if (auto d = int(this._storage.id) - int(rhs._storage.id))
                return d;
            switch (_storage.id)
            {
                static foreach (i, T; AllowedTypes)
                {
                    case i:
                        static if (__traits(compiles, __cmp(trustedGet!T, rhs.trustedGet!T)))
                            return __cmp(trustedGet!T, rhs.trustedGet!T);
                        else
                        static if (__traits(hasMember, T, "opCmp") && !is(T == U*, U))
                            return this.trustedGet!T.opCmp(rhs.trustedGet!T);
                        else
                        // static if (isFloatingPoint!T)
                        //     return trustedGet!T == rhs ? 0 : trustedGet!T - rhs.trustedGet!T;
                        // else
                            return this.trustedGet!T < rhs.trustedGet!T ? -1 :
                                this.trustedGet!T > rhs.trustedGet!T ? +1 : 0;
                }
                default: assert(0);
            }
        }
    }

    /// Requires mir-algorithm package
    void toString(W)(scope ref W w) const
    {
        static if (AllowedTypes.length == 0)
        {
            return w.put(cast(immutable C[])"Algebraic");
        }
        else
        {
            static assert (__traits(compiles, {import mir.format: print;}), "Algebraic.toString requires mir-algorithm package");
            import mir.format: print;
            switch (_storage.id)
            {
                static foreach (i, P; _Payload)
                {
                    case i:
                        print(w, _storage.payload[i]);
                        return;
                }
                default: assert(0);
            }
        }
    }

    static if (is(AllowedTypes[0] == typeof(null)))
    {
        ///
        bool opCast(C)() const
            if (is(C == bool))
        {
            return _storage.id != 0;
        }
        /// Defined if the first type is `typeof(null)`
        bool isNull() const { return _storage.id == 0; }
        /// ditto
        void nullify() { this = null; }

        /// ditto
        auto get()()
            if (allSatisfy!(isCopyable, AllowedTypes[1 .. $]) && AllowedTypes.length != 2)
        {
            if (!_storage.id)
            {
                version(D_Exceptions)
                    throw variantNullException;
                else
                    assert(0, variantNullExceptionMsg);
            }
            static if (AllowedTypes.length > 1)
            {
                Algebraic!(
                    _setId,
                    _TypeSets[0 .. _setId],
                    TypeSet!(TemplateArgsOf!(_TypeSets[_setId])[1 .. $]),
                    _TypeSets[_setId + 1 .. $]
                ) ret;
                static if (ret.AllowedTypes.length > 1)
                    ret._storage.id = cast(typeof(ret._storage.id))(this._storage.id - 1);

                static if (anySatisfy!(hasElaborateCopyConstructor, AllowedTypes))
                {
                    ret._storage.bytes = 0;
                    S: switch (_storage.id)
                    {
                        static foreach (i, T; AllowedTypes)
                        {
                            static if (hasElaborateCopyConstructor!T)
                            {
                                case i:
                                    ret.trustedGet!T.emplaceRef(this.trustedGet!T);
                                    break S;
                            }
                        }
                        default:
                            ret._storage.bytes = this._storage.bytes[0 .. ret._storage.bytes.length];
                    }
                }
                else
                {
                    ret._storage.bytes = this._storage.bytes[0 .. ret._storage.bytes.length];
                }

                return ret;
            }
        }

        static if (AllowedTypes.length == 2)
        {
            /++
            Gets the value if not null. If `this` is in the null state, and the optional
            parameter `fallback` was provided, it will be returned. Without `fallback`,
            calling `get` with a null state is invalid.
        
            When the fallback type is different from the Nullable type, `get(T)` returns
            the common type.
        
            Params:
                fallback = the value to return in case the `Nullable` is null.
        
            Returns:
                The value held internally by this `Nullable`.
            +/
            ref inout(AllowedTypes[1]) get() inout
            {
                assert(_storage.id, "Called `get' on null Nullable!(" ~ AllowedTypes[1].stringof ~ ").");
                return trustedGet!(AllowedTypes[1]);
            }

            /// ditto
            @property inout(AllowedTypes[1]) get()(inout(AllowedTypes[1]) fallback) inout @safe pure nothrow
            {
                return isNull ? fallback : get();
            }

            /// ditto
            @property auto get(U)(inout(U) fallback) inout @safe pure nothrow
            {
                return isNull ? fallback : get();
            }
        }
    }

    static foreach (i, T; AllowedTypes)
    {
        /// Zero cost always nothrow `get` alternative
        auto ref trustedGet(E)() @trusted @property return inout nothrow
            if (is(E == T))
        {
            assert (i == _storage.id);
            static if (is(T == typeof(null)))
                return null;
            else
            static if (is(T == void))
                return;
            else
                return _storage.payload[i];
        }

        private auto ref T _mutableTrustedGet(E)() @trusted @property return const nothrow
            if (is(E == T))
        {
            assert (i == _storage.id, T.stringof);
            static if (is(T == typeof(null)))
                return null;
            else
            static if (is(T == void))
                return;
            else
                return *cast(Unqual!(AllowedTypes[i])*)&_storage.payload[i];
        }

        /++
        Throws: Exception if the storage contains value of other type
        +/
        auto ref get(E)() @property return inout
            if (is(E == T))
        {
            import mir.utility: _expect;
            static if (AllowedTypes.length > 1)
            {
                if (_expect(i != _storage.id, false))
                {
                    version(D_Exceptions)
                        throw variantException;
                    else
                        assert(0, variantExceptionMsg);
                }
            }
            return trustedGet!T;
        }

        /++
        Checks if the storage stores an allowed type.
        +/
        bool _is(E)() const @property nothrow @nogc
            if (is(E == T))
        {
            return _storage.id == i;
        }

        static if (is(T == void))
        /// Defined if `AllowedTypes` contains `void`
        static Algebraic _void()
        {
            Algebraic ret;
            ret._storage.bytes = 0;
            ret._storage.id = i;
            return ret;
        }
        else
        {

        private void inoutTrustedCtor(ref scope inout T rhs) inout @trusted
        {
            trustedBytes[0 .. _Payload[i].sizeof] = *cast(ubyte[_Payload[i].sizeof]*)&rhs;
            trustedBytes[_Payload[i].sizeof .. $] = 0;
            static if (AllowedTypes.length > 1)
                *cast(typeof(_Storage.id)*)&_storage.id = i;
            static if (hasOpPostMove!T)
                (*cast(Unqual!T*)&(trustedGet!T())).opPostMove(rhs);
            static if (hasElaborateDestructor!T)
                emplaceRef(*cast(Unqual!T*)&rhs);
        }

        ///
        this(T rhs)
        {
            inoutTrustedCtor(rhs);
        }

        /// ditto
        this(const T rhs) const
        {
            inoutTrustedCtor(rhs);
        }

        /// ditto
        this(immutable T rhs) immutable
        {
            inoutTrustedCtor(rhs);
        }

        static if (__traits(compiles, (ref T a, ref T b) { moveEmplace(a, b); }))
        ///
        ref opAssign(T rhs) return @trusted
        {
            static if (anySatisfy!(hasElaborateDestructor, AllowedTypes))
                this.__dtor();
            __ctor(rhs);
            return this;
        }

        /++
        +/
        auto opEquals()(auto ref const T rhs) const
        {
            static if (AllowedTypes.length > 1)
                if (_storage.id != i)
                    return false;
            return trustedGet!T == rhs;
        } 

        /++
        +/
        auto opCmp()(auto ref const T rhs) const
        {
            import mir.internal.utility: isFloatingPoint;
            static if (AllowedTypes.length > 1)
                if (auto d = int(_storage.id) - int(i))
                    return d;
            static if (__traits(compiles, __cmp(trustedGet!T, rhs)))
                return __cmp(trustedGet!T, rhs);
            else
            static if (__traits(hasMember, T, "opCmp") && !is(T == U*, U))
                return trustedGet!T.opCmp(rhs);
            else
            static if (isFloatingPoint!T)
                return trustedGet!T == rhs ? 0 : trustedGet!T - rhs;
            else
                return trustedGet!T < rhs ? -1 :
                    trustedGet!T > rhs ? +1 : 0;
        }
        }
    }
}

/// Checks toString
/// Algerbraic.toString requries mir-algorithm package
@safe pure nothrow version(mir_core_test) unittest
{
    static if (__traits(compiles, { import mir.format; }))
    {
        import mir.conv: to;

        alias V = Nullable!(void, int);
        static assert(is(V == Variant!(typeof(null), void, int)));

        V variant;
        assert(variant.to!string == "null");

        variant = V._void;
        assert(variant.to!string == "void");

        variant = 5;
        assert(variant.to!string == "5");
    }
}

/++
Variant Type (aka Algebraic Type) with clever member access.

Compatible with BetterC mode.
+/
alias Variant(T...) = Algebraic!(0, TypeSet!T);

/++
Nullable variant Type (aka Algebraic Type) with clever member access.

Compatible with BetterC mode.
+/
alias Nullable(T...) = Variant!(typeof(null), T);

// example from std.variant
/++
$(H4 Self-Referential Types)
A useful and popular use of algebraic data structures is for defining
$(LUCKY self-referential data structures), i.e. structures that embed references to
values of their own type within.
This is achieved with $(LREF Variant) by using $(LREF This) as a placeholder whenever a
reference to the type being defined is needed. The $(LREF Variant) instantiation
will perform $(LINK2 https://en.wikipedia.org/wiki/Name_resolution_(programming_languages)#Alpha_renaming_to_make_name_resolution_trivial,
alpha renaming) on its constituent types, replacing $(LREF This)
with the self-referenced type. The structure of the type involving $(LREF This) may
be arbitrarily complex.
+/
@safe pure version(mir_core_test) unittest
{
    import mir.functional: Tuple = RefTuple;

    // A tree is either a leaf or a branch of two others
    alias Tree(Leaf) = Variant!(Leaf, Tuple!(This*, This*));
    alias Leafs = Tuple!(Tree!int*, Tree!int*);

    Tree!int tree = Leafs(new Tree!int(41), new Tree!int(43));
    Tree!int* right = tree.get!Leafs[1];
    assert(*right == 43);
}

///ditto
@safe pure version(mir_core_test) unittest
{
    // An object is a double, a string, or a hash of objects
    alias Obj = Variant!(double, string, This[string]);
    alias Map = Obj[string];

    Obj obj = "hello";
    assert(obj._is!string);
    assert(obj.trustedGet!string == "hello");
    obj = 42.0;
    assert(obj.get!double == 42);
    obj = ["customer": Obj("John"), "paid": Obj(23.95)];
    assert(obj.get!Map["customer"] == "John");
}

@safe pure @nogc nothrow
version(mir_core_test) unittest
{
    import core.stdc.string: memcmp;

    static struct C(ubyte payloadSize, bool isPOD, bool hasToHash = true, bool hasOpEquals = true)
    {
        ubyte[payloadSize] _payload;

    const:

        static if (!isPOD)
        {
            this(this) {}
            ~this() {}
        }

    @safe pure nothrow @nogc:


    static if (hasToHash)
        size_t toHash() { return hashOf(_payload); }

    static if (hasOpEquals)
        auto opEquals(ref const typeof(this) rhs) @trusted { return memcmp(_payload.ptr, rhs._payload.ptr, _payload.length); }
        auto opCmp(ref const typeof(this) rhs) { return _payload == rhs._payload; }
    }

    static foreach (size1; [1, 2, 4, 8, 10, 16, 20])
    static foreach (size2; [1, 2, 4, 8, 10, 16, 20])
    static if (size1 != size2)
    static foreach (isPOD; [true, false])
    static foreach (hasToHash; [true, false])
    static foreach (hasOpEquals; [true, false])
    {{
        alias T = Variant!(
                double,
                C!(size1, isPOD, hasToHash, hasOpEquals),
                C!(size2, isPOD, hasToHash, hasOpEquals));
        static assert (__traits(compiles, T.init <= T.init));
    }}
}

/// const propogation
@safe pure nothrow @nogc
version(mir_core_test) unittest
{
    static struct S1 { immutable(ubyte)* value; }
    static struct C1 { immutable(uint)* value; }

    alias V = Variant!(S1, C1);
    const V v = S1();
    assert(v._is!S1);
    V w = v;
    w = v;

    immutable f = V(S1());
    auto t = immutable V(S1());
    // auto j = immutable V(t);
    // auto i = const V(t);
}

/// ditto
@safe pure nothrow @nogc
version(mir_core_test) unittest
{
    static struct S2 {
        uint* value;
        this(return ref scope const typeof(this) rhs) {}
        ref opAssign(typeof(this) rhs) return { return this; }
    }
    static struct C2 { const(uint)* value; }

    alias V = Variant!(S2, C2);
    const V v = S2();
    V w = v;
    w = S2();
    w = v;
    w = cast(const) V.init;

    const f = V(S2());
    auto t = const V(f);
}


@safe pure nothrow @nogc
version(mir_core_test) unittest
{
    static struct S3 {
        uint* value;
        this(return ref scope typeof(this) rhs) {}
        this(return ref scope const typeof(this) rhs) const {}
        this(return ref scope immutable typeof(this) rhs) immutable {}
    }
    static struct C3 { immutable(uint)* value; }

    S3 s;
    S3 r = s;
    r = s;
    r = S3.init;

    alias V = Variant!(S3, C3);
    V v = S3();
    V w = v;
    w = S3();
    w = V.init;
    w = v;

    immutable V e = S3();
    auto t = immutable V(S3());
    auto j = const V(t);
    auto h = t;

    immutable V l = C3();
    auto g = immutable V(C3());
}

@safe pure nothrow @nogc
version(mir_core_test) unittest
{
    static struct S4 {
        uint* value;
        this(return ref scope const typeof(this) rhs) pure immutable {}
    }
    static struct C4 { immutable(uint)* value; }


    S4 s;
    S4 r = s;
    r = s;
    r = S4.init;

    alias V = Variant!(S4, C4);
    V v = S4();
    V w = v;
    w = S4();
    w = V.init;
    w = v;

    {
        const V e = S4();
        const k = w;
        auto t = const V(k);
        auto j = immutable V(k);
    }

    immutable V e = S4();
    immutable k = w;
    auto t = immutable V(S4());
    auto j = const V(t);
    auto h = t;

    immutable V l = C4();
    import core.lifetime;
    auto g = immutable V(C4());
    immutable b = immutable V(s);
}

@safe pure nothrow @nogc
version(mir_core_test) unittest
{
    import core.lifetime: move;

    static struct S5 {
        immutable(uint)* value;
        this(return ref scope typeof(this) rhs) {}
        this(return ref scope const typeof(this) rhs) immutable {}
    }
    static struct C5 { immutable(uint)* value; }

    S5 s;
    S5 r = s;
    r = s;
    r = S5.init;

    alias V = Variant!(S5, C5);
    V v = S5();
    V w = v;
    w = S5();
    w = V.init;
    w = v;

    immutable V e = S5();
    immutable f = V(S5());
    immutable k = w;
    auto t = immutable V(S5());
    auto j = const V(t);
    auto h = t;

    immutable V l = C5();
    import core.lifetime;
    immutable n = w.move;
    auto g = immutable V(C5());
    immutable b = immutable V(s);
}

@safe pure nothrow @nogc
version(mir_core_test) unittest
{
    static struct S {
        uint* value;
        this(this) @safe pure nothrow @nogc {}
        // void opAssign(typeof(this) rhs) {}
    }
    static struct C { const(uint)* value; }

    S s;
    S r = s;
    r = s;
    r = S.init;

    alias V = Variant!(S, C);
    V v = S();
    V w = v;
    w = S();
    w = V.init;
    w = v;
}

/++
Applies a delegate or function to the given Variant depending on the held type,
ensuring that all types are handled by the visiting functions.
+/
alias match(visitors...) = visit!(naryFun!visitors, Exhaustive.compileTime);

///
@safe pure @nogc nothrow
version(mir_core_test) unittest
{
    alias Number = Variant!(int, double);

    Number x = 23;
    Number y = 1.0;

    assert(x.match!((int v) => true, (float v) => false));
    assert(y.match!((int v) => false, (float v) => true));
}

/// Special `typeof(null)` support for the first argument.
@safe pure @nogc
version(mir_core_test) unittest
{
    Nullable!int a = 5;
    assert(a.get!int == 5);
    a.nullify;
    assert(a.isNull);
    a = 4;
    assert(!a.isNull);
    assert(a.get == 4);
    assert(a == 4);
    a = 4;
    a = null;
    assert(a == null);
}

/// ditto
@safe pure @nogc
version(mir_core_test) unittest
{
    alias Number = Nullable!(int, double);

    Number z = null; // default
    Number x = 23;
    Number y = 1.0;

    () nothrow {
        assert(x.match!((int v) => true, (float v) => false));
        assert(y.match!((int v) => false, (float v) => true));
        assert(z.match!((typeof(null) v) => true, (v) => false));
    } ();

    auto xx = x.get;
    static assert (is(typeof(xx) == Variant!(int, double)));
    assert(xx.match!((int v) => v, (float v) => 0) == 23);
    assert(xx.match!((ref v) => v) == 23);

    x = null;
    y.nullify;

    assert(x.isNull);
    assert(y.isNull);
    assert(z.isNull);
    assert(z == y);
}

// Type with copy constructor
@safe pure nothrow @nogc 
version(mir_core_test) unittest 
{
    static struct S
    {
        int n;
        this(ref return scope inout S rhs) inout
        {
            this.n = rhs.n + 1;
        }
    }

    Variant!S a = S();
    auto b = a;

    import mir.conv;
    assert(b.get!S.n == 1);
    assert(a.get!S.n == 0);
}

// Empty type set
@safe pure nothrow @nogc version(mir_core_test) unittest 
{
    Variant!() a;
    auto b = a;
    assert(a.toHash == 0);
    assert(a == b);
    assert(a <= b && b >= a);
    static assert(typeof(a).sizeof == 1);
}

// Empty nullable type set
@safe pure nothrow @nogc version(mir_core_test) unittest 
{
    Nullable!() a;
    auto b = a;
    assert(a.toHash == 0);
    assert(a == b);
    assert(a <= b && b >= a);
    static assert(typeof(a).sizeof == 1);
}

// Small types
@safe pure nothrow @nogc version(mir_core_test) unittest 
{
    struct S { ubyte d; }
    static assert(Nullable!(byte, char, S).sizeof == 2);
}

// Alignment
@safe pure nothrow @nogc version(mir_core_test) unittest 
{
    struct S { ubyte[3] d; }
    static assert(Nullable!(ushort, wchar, S).sizeof == 4);
}

// opPostMove support
@safe pure @nogc nothrow
version(mir_core_test) unittest
{
    import std.algorithm.mutation: move;

    static struct S
    {
        uint s;

        void opPostMove(const ref S old) nothrow
        {
            this.s = old.s + 1;
        }
    }

    Variant!S a;

    auto b = a.move;
    assert(b.get!S.s == 1);
}

/++
Behaves as $(LREF match) but doesn't enforce at compile time that all types can be handled by the visiting functions.
Throws: Exception if `naryFun!visitors` can't be called with provided arguments
+/
alias tryMatch(visitors...) = visit!(naryFun!visitors, Exhaustive.exception);

///
@safe pure @nogc
version(mir_core_test) unittest
{
    alias Number = Variant!(int, double);

    Number x = 23;

    assert(x.tryMatch!((int v) => true));
}

/++
Behaves as $(LREF match) but doesn't enforce at compile time that all types can be handled by the visiting functions.
Returns: nullable variant, null value is used if `naryFun!visitors` can't be called with provided arguments 
+/
alias optionalMatch(visitors...) = visit!(naryFun!visitors, Exhaustive.nullable);

///
@safe pure @nogc nothrow
version(mir_core_test) unittest
{
    static struct S { int a; }

    Variant!(S, double) variant;

    alias optionalMatchInst = optionalMatch!((ref value) => value + 0);

    // do nothing because of variant isn't initialized
    Nullable!double result = optionalMatchInst(variant);
    assert(result.isNull);

    variant = S(2);
    // do nothing because of lambda can't compile
    result = optionalMatchInst(variant);
    assert(result == null);

    variant = 3.0;
    result = optionalMatchInst(variant);
    assert (result == 3.0);
}

/++
Applies a member handler to the given Variant depending on the held type,
ensuring that all types are handled by the visiting handler.
+/
alias getMember(string member) = visit!(getMemberHandler!member, Exhaustive.compileTime);

///
@safe pure @nogc nothrow
version(mir_core_test) unittest
{
    static struct S { auto bar(int a) { return a; }}
    static struct C { alias bar = (double a) => a * 2; }

    alias V = Variant!(S, C);

    V x = S();
    V y = C();

    static assert(is(typeof(x.getMember!"bar"(2)) == Variant!(int, double)));
    assert(x.getMember!"bar"(2) == 2);
    assert(y.getMember!"bar"(2) != 4);
    assert(y.getMember!"bar"(2) == 4.0);
}

/++
Behaves as $(LREF match) but doesn't enforce at compile time that all types can be handled by the member visitor.
Throws: Exception if member can't be accessed with provided arguments
+/
alias tryGetMember(string member) = visit!(getMemberHandler!member, Exhaustive.exception);

///
@safe pure @nogc
version(mir_core_test) unittest
{
    static struct S { int bar(int a) { return a; }}
    static struct C { alias Bar = (double a) => a * 2; }

    alias V = Variant!(S, C);

    V x = S();
    V y = C();

    static assert(is(typeof(x.tryGetMember!"bar"(2)) == int));
    static assert(is(typeof(y.tryGetMember!"Bar"(2)) == double));
    assert(x.tryGetMember!"bar"(2) == 2);
    assert(y.tryGetMember!"Bar"(2) == 4.0);
}

///
@safe pure @nogc nothrow
version(mir_core_test) unittest
{
    alias Number = Variant!(int, double);

    Number x = Number(23);
    Number y = Number(1.0);

    assert(x.match!((int v) => true, (float v) => false));
    assert(y.match!((int v) => false, (float v) => true));
}

/++
Behaves as $(LREF match) but doesn't enforce at compile time that all types can be handled by the member visitor.
Returns: nullable variant, null value is used if member can't be called with provided arguments 
+/
alias optionalGetMember(string member) = visit!(getMemberHandler!member, Exhaustive.nullable);


private template getMemberHandler(string member)
{
    ///
    auto ref getMemberHandler(V, Args...)(ref V value, auto ref Args args)
    {
        static if (Args.length == 0)
        {
            return __traits(getMember, value, member);
        }
        else
        {
            import core.lifetime: forward;
            return __traits(getMember, value, member)(forward!args);
        }
    }
}

private template VariantReturnTypes(T...)
{
    import std.meta: NoDuplicates, staticMap;

    alias VariantReturnTypes = NoDuplicates!(staticMap!(TryRemoveConst, T));
}

enum Exhaustive
{
    compileTime,
    exception,
    nullable,
}

private template visit(alias visitor, Exhaustive exhaustive)
{
    import std.traits: Unqual;
    ///
    auto ref visit(V, Args...)(auto ref V variant, auto ref Args args)
        if (isVariant!V)
    {
        import core.lifetime: forward;
        import std.meta: NoDuplicates, staticMap, AliasSeq;

        template allArgs(T)
        {
            static if (is(T == void))
                alias allArgs = forward!args;
            else
            static if (is(T == typeof(null)))
                alias allArgs = AliasSeq!(null, forward!args);
            else
            {
                ref fun() @property @trusted
                {
                    return variant.trustedGet!T;
                }
                alias allArgs = AliasSeq!(fun, forward!args);
            }
        }

        template VariantReturnTypesImpl(T)
        {
            static if (__traits(compiles, visitor(allArgs!T)))
                alias VariantReturnTypesImpl = TryRemoveConst!(typeof(visitor(allArgs!T)));
            else
                alias VariantReturnTypesImpl = AliasSeq!();
        }

        static if (exhaustive == Exhaustive.nullable)
            alias AllReturnTypes = NoDuplicates!(typeof(null), staticMap!(VariantReturnTypesImpl, V.AllowedTypes));
        else
            alias AllReturnTypes = NoDuplicates!(staticMap!(VariantReturnTypesImpl, V.AllowedTypes));

        switch (variant._storage.id)
        {
            static foreach (i, T; V.AllowedTypes)
            {
                case i:
                    static if (__traits(compiles, visitor(allArgs!T)))
                    {
                        static if (AllReturnTypes.length == 1)
                        {
                            return visitor(allArgs!T);
                        }
                        else
                        {
                            static if (is(VariantReturnTypesImpl!T == void))
                            {
                                visitor(allArgs!T);
                                return Variant!AllReturnTypes.init;
                            }
                            else
                            {
                                return Variant!AllReturnTypes(visitor(allArgs!T));
                            }
                        }
                    }
                    else
                    static if (exhaustive == Exhaustive.compileTime)
                    {
                        static if (is(T == typeof(null)))
                            assert(0, "Null " ~ V.stringof);
                        else
                            static assert(0, V.stringof ~ ": the visitor cann't be caled with type (first argument) " ~ typeof(variant.trustedGet!T()).stringof ~ (Args.length ? (" and additional arguments " ~ Args.stringof) : ""));
                    }
                    else
                    static if (exhaustive == Exhaustive.nullable)
                    {
                        return Variant!AllReturnTypes(null);
                    }
                    else
                    {
                        version(D_Exceptions)
                            throw variantMemberException;
                        else
                            assert(0, variantMemberExceptionMsg);
                    }
            }
            default: assert(0);
        }
    }
}

@safe pure @nogc
version(mir_core_test) unittest
{
    static struct S { int a; }

    Variant!(S, double) variant;
    variant = 1.0;
    variant.tryMatch!((ref value, b) => value += b)(2);
    assert (variant.get!double == 3);

    alias fun = (ref value) {
        static if (is(typeof(value) == S))
            value.a += 2;
        else
           value += 2;
    };

    variant.tryMatch!fun;
    assert (variant.get!double == 5);

    variant = S(4);
    variant.tryMatch!fun;
    assert (variant.get!S.a == 6);
}
