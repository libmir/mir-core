/++
$(H2 Variant and Nullable types)

This module implements a
$(HTTP erdani.org/publications/cuj-04-2002.php.html,discriminated union)
type (a.k.a.
$(HTTP en.wikipedia.org/wiki/Tagged_union,tagged union),
$(HTTP en.wikipedia.org/wiki/Algebraic_data_type,algebraic type)).
Such types are useful
for type-uniform binary interfaces, interfacing with scripting
languages, and comfortable exploratory programming.

The module defines generic $(LREF Algebraic) type that contains a payload.
The allowed types of the paylad are defined by the unordered $(LREF TypeSet).

$(LREF Algebraic) template accepts two arguments: self type set id and a list of type sets.

$(BOOKTABLE $(H3 $(LREF Algebraic) Aliases),
$(TR $(TH Name) $(TH Description))
$(T2 Variant, an algebraic type for a single type set)
$(T2 Nullable, an algebraic type for a single type set with at least `typeof(null)`)
$(T2 Variants, a list of algebraic types with cyclic type referencing, which defined over the same list of type sets)
)

$(BOOKTABLE $(H3 $(LREF Algebraic) Traits),
$(TR $(TH Name) $(TH Description))
$(T2 isVariant, an algebraic type)
$(T2 isNullable, an algebraic type with at least `typeof(null)` in the self type set. )
)

$(BOOKTABLE $(H3 Special Types),
$(TR $(TH Name) $(TH Description))
$(T2plain `void`, It is usefull to indicate a possible return type of the visitor. Can't be accesed by reference. )
$(T2plain `typeof(null)`, It is usefull for nullable types. Also, it is used to indicate that a visitor can't match the current value of the algebraic. Can't be accesed by reference. )
$(T2 This, An dummy structure that is used to construct self-referencing algebraic types. Example: `Variant!(int, double, string, This*[2])`)
$(T2plain $(LREF SetAlias)`!setId`, An dummy structure that is used to construct cyclic-referencing lists of algebraic types. )
)

$(BOOKTABLE $(H3 Visitor Handlers),
$(TR $(TH Name) $(TH Checks can compile) $(TH Throws if no match) $(TH Returns $(LREF Nullable)) $(TH Multiple dispatch) $(TH Argumments count) $(TH Algebraic first argument))
$(T7 visit, Yes, N/A, No, No, 1+, Yes)
$(T7 optionalVisit, No, No, Yes, No, 1+, Yes)
$(T7 autoVisit, No, No, auto, No, 1+, Yes)
$(T7 tryVisit, No, Yes, No, No, 1+, Yes)
$(T7 match, Yes, N/A, No, Yes, 0+, Yes/No)
$(T7 optionalMatch, No, No, Yes, Yes, 0+, Yes/No)
$(T7 autoMatch, No, No, auto, Yes, 0+, Yes/No)
$(T7 tryMatch, No, Yes, No, Yes, 0+, Yes/No)
$(T7 getMember, Yes, N/A, No, No, 1+, Yes)
$(T7 optionalGetMember, No, No, Yes, No, 1+, Yes)
$(T7 autoGetMember, No, No, auto, No, 1+, Yes)
$(T7 tryGetMember, No, Yes, No, No, 1+, Yes)
)

$(H3 Type Set)
$(UL 
$(LI Type set is unordered. Example:`TypeSet!(int, double)` and `TypeSet!(double, int)` are the same. )
$(LI Duplicats are ignored. Example: `TypeSet!(float, int, float)` and `TypeSet!(int, float)` are the same. )
$(LI Types are automatically unqualified if this operation can be performed implicitly. Example: `TypeSet!(const int) and `TypeSet!int` are the same. )
$(LI Non trivial `TypeSet!(A, B, ..., etc)` is allowed.)
$(LI Trivial `TypeSet!T` is allowed.)
$(LI Empty `TypeSet!()` is allowed.)
)

$(H3 Visitors)
$(UL 
$(LI Visitors are allowed to return values of different types If there are more then one return type then the an $(LREF Algebraic) type is returned. )
$(LI Visitors are allowed to accept additional arguments. The arguments can be passed to the visitor handler. )
$(LI Multiple visitors can be passes to the visitor handler. )
$(LI Visitors are matched according to the common $(HTTPS dlang.org/spec/function.html#function-overloading, Dlang Function Overloading) rules. )
$(LI Visitors are allowed accept algebraic value by reference except the value of `typeof(null)`. )
$(LI Visitors are called without algebraic value if its algebraic type is `void`. )
$(LI If the visitors arguments has known types, then such visitors should be passed to a visitor handler before others to make the compiler happy. This includes visitors with no arguments, which is used to match `void` type. )
)

$(H3 Implementation Features)
$(UL 
$(LI BetterC support. Runtime `TypeInfo` is not used.)
$(LI Copy-constructors and postblit constructors are supported. )
$(LI `toHash`, `opCmp`. `opEquals`, and `toString` support. )
$(LI No string or template mixins are used. )
$(LI Optimised for fast execution. )
)

See_also: $(HTTPS en.wikipedia.org/wiki/Algebra_of_sets, Algebra of sets).

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: Ilya Yaroshenko

Macros:
T2plain=$(TR $(TDNW $1) $(TD $+))
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
T4=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4))
T7=$(TR $(TDNW $(LREF $1)) $(TD $2) $(TD $3) $(TD $4) $(TD $5) $(TD $6) $(TD $7))

+/
module mir.algebraic;

import mir.functional: naryFun;
import std.meta: allSatisfy;

private static immutable variantExceptionMsg = "mir.algebraic: the algebraic stores other type then requested.";
private static immutable variantNullExceptionMsg = "mir.algebraic: the algebraic is empty and doesn't store any value.";
private static immutable variantMemberExceptionMsg = "mir.algebraic: the algebraic is stores the type that isn't compatible with the user provided visitor and arguments.";

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
static if (__VERSION__ < 2094)
    private enum isCopyable(S) = is(typeof({ S foo = S.init; S copy = foo; }));
else
    private enum isCopyable(S) = __traits(isCopyable, S); 
private enum isPOD(T) = __traits(isPOD, T);
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

private static struct _Null()
{
@safe pure nothrow @nogc const:
    int opCmp(_Null) { return 0; }
    this(typeof(null)) inout {}
    string toString() { return "null"; }
}

private static struct _Void()
{
 @safe pure nothrow @nogc const:
    int opCmp(_Void) { return 0; }
    string toString() { return "void"; }
}

///
enum isVariant(T) = __traits(hasMember, T, "_isVariant");

///
unittest
{
    static assert(isVariant!(Variant!(int, string)));
    static assert(isVariant!(Nullable!(int, string)));
    static assert(!isVariant!int);
}

///
enum isNullable(T) = isVariant!T && __traits(hasMember, T, "nullify");

///
unittest
{
    static assert(!isNullable!(Variant!(int, string)));
    static assert(isNullable!(Nullable!(int, string)));
    static assert(isNullable!(Nullable!()));
    static assert(!isNullable!int);
}

/++
Dummy type for $(LREF Variants) self-referencing.
+/
struct SetAlias(uint id)
{
@safe pure nothrow @nogc const:
    int opCmp(typeof(this)) { return 0; }
    string toString() { return typeof(this).stringof; }
}

/++
Dummy type for $(LREF Variant) and $(LREF Nullable) self-referencing.
+/
struct This
{
@safe pure nothrow @nogc const:
    int opCmp(typeof(this)) { return 0; }
    string toString() { return typeof(this).stringof; }
}


// example from std.variant
/++
$(H4 Self-Referential Types)
A useful and popular use of algebraic data structures is for defining
$(LUCKY self-referential data structures), i.e. structures that embed references to
values of their own type within.
This is achieved with $(LREF Variant) by using $(LREF This) as a placeholder whenever a
reference to the type being defined is needed. The $(LREF Variant) instantiation
will perform 
$(LINK2 https://en.wikipedia.org/wiki/Name_resolution_(programming_languages)#Alpha_renaming_to_make_name_resolution_trivial,
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

///
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


/++
Type set for $(LREF Variants) self-referencing.
+/
template TypeSet(T...)
{
    import std.meta: staticSort, staticMap;
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
        alias TypeSet = TypeSet!(staticMap!(TryRemoveConst, T));
}

///
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
will perform 
$(LINK2 https://en.wikipedia.org/wiki/Name_resolution_(programming_languages)#Alpha_renaming_to_make_name_resolution_trivial,
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
    alias V = Variants!(
        TypeSet!(string, long, SetAlias!1*), // string, long, and pointer to V[1] type
        TypeSet!(SetAlias!0[], int), // int and array of V[0] type elements
    );

    alias A = V[0];
    alias B = V[1];

    A arr = new B([A("hey"), A(100)]);
    assert(arr._is!(B*));
    assert(arr.trustedGet!(B*)._is!(A[]));
}

/++
Variant Type (aka Algebraic Type).

Compatible with BetterC mode.
+/
alias Variant(T...) = Algebraic!(0, TypeSet!T);

///
@safe pure @nogc 
version(mir_core_test) unittest
{
    Variant!(int, double, string) v = 5;
    assert(v.get!int == 5);
    v = 3.14;
    assert(v == 3.14);
    // auto x = v.get!long; // won't compile, type long not allowed
    // v = '1'; // won't compile, type char not allowed
}

/// Single argument Variant
// and Type with copy constructor
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

/// Empty type set
@safe pure nothrow @nogc version(mir_core_test) unittest 
{
    Variant!() a;
    auto b = a;
    assert(a.toHash == 0);
    assert(a == b);
    assert(a <= b && b >= a);
    static assert(typeof(a).sizeof == 1);
}

/// Small types
@safe pure nothrow @nogc version(mir_core_test) unittest 
{
    struct S { ubyte d; }
    static assert(Nullable!(byte, char, S).sizeof == 2);
}

/// Clever packaging
@safe pure nothrow @nogc version(mir_core_test) unittest 
{
    struct S { ubyte[3] d; }
    static assert(Nullable!(ushort, wchar, S).sizeof == 4);
}

/// opPostMove support
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
Nullable $(LREF Variant) Type (aka Algebraic Type).

The impllementation is defined as
```
alias Nullable(T...) = Variant!(typeof(null), T);
```

In additional to common algebraic API the following members can be accesssed:
$(UL 
$(LI $(LREF .Algebraic.isNull))
$(LI $(LREF .Algebraic.nullify))
$(LI $(LREF .Algebraic.get.2))
)

Compatible with BetterC mode.
+/
alias Nullable(T...) = Variant!(typeof(null), T);

/++
Single type `Nullable`
+/
@safe pure @nogc
version(mir_core_test) unittest
{
    static assert(is(Nullable!int == Variant!(typeof(null), int)));
    
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

/// Empty nullable type set support
@safe pure nothrow @nogc version(mir_core_test) unittest 
{
    Nullable!() a;
    auto b = a;
    assert(a.toHash == 0);
    assert(a == b);
    assert(a <= b && b >= a);
    static assert(typeof(a).sizeof == 1);
}

/++
Implementation of $(LREF Variant), $(LREF Variants), and $(LREF Nullable).
+/
struct Algebraic(uint _setId, _TypeSets...)
    if (allSatisfy!(isInstanceOf!TypeSet, _TypeSets) && _setId < _TypeSets.length)
{
    private enum _isVariant;

    import core.lifetime: moveEmplace;
    import mir.conv: emplaceRef;
    import std.meta: AliasSeq, anySatisfy, allSatisfy, staticMap, templateOr;
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

    static if (anySatisfy!(hasElaborateDestructor, _Payload))
    ~this() @trusted
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

    static if (anySatisfy!(hasOpPostMove, _Payload))
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
        static if (!__traits(compiles, (){ _Payload[0] arg; }))
        {
            @disable this();
        }
    }

    private ref trustedBytes() inout @trusted
    {
        return *cast(ubyte[_storage.bytes.length]*)&this._storage.bytes;
    }

    ///
    this(uint rhsId, RhsTypeSets...)(Algebraic!(rhsId, RhsTypeSets) rhs)
        if (allSatisfy!(Contains!AllowedTypes, Algebraic!(rhsId, RhsTypeSets).AllowedTypes))
    {
        this._storage.allBytes[0 .. rhs._storage.allBytes.length] = rhs._storage.allBytes;
        this._storage.allBytes[rhs._storage.allBytes.length .. $] = 0;
        static if (hasElaborateDestructor!(Algebraic!(rhsId, RhsTypeSets)))
            rhs._storage.allBytes = Algebraic!(rhsId, RhsTypeSets).init._storage.allBytes;
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
                        static if (__VERSION__ < 2094)
                            CopyTypeQualifiers!(RhsAlgebraic, _StorageI!i) storage = CopyTypeQualifiers!(RhsAlgebraic, _StorageI!i)( rhs._storage.payload[i] );
                        else
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
    string toString()() const
    {
        static if (AllowedTypes.length == 0)
        {
            return "Algebraic";
        }
        else
        {
            import mir.conv: to;
            switch (_storage.id)
            {
                static foreach (i, P; _Payload)
                {
                    case i:
                        static if (__traits(compiles, { auto s = to!string(_storage.payload[i]);}))
                            return to!string(_storage.payload[i]);
                        else
                            return AllowedTypes[i].stringof;
                }
                default: assert(0);
            }
        }
    }

    ///ditto
    void toString(W)(scope ref W w) const
    {
        static if (AllowedTypes.length == 0)
        {
            return w.put("Algebraic");
        }
        else
        {
            switch (_storage.id)
            {
                static foreach (i, P; _Payload)
                {
                    case i:
                        static if (__traits(compiles, { import mir.format: print; print(w, _storage.payload[i]); }))
                            { import mir.format: print; print(w, _storage.payload[i]); }
                        else
                            w.put(AllowedTypes[i].stringof);
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
            import mir.utility: _expect;
            if (_expect(!_storage.id, false))
            {
                throw variantNullException;
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
            auto ref inout(AllowedTypes[1]) get() inout
            {
                assert(_storage.id, "Called `get' on null Nullable!(" ~ AllowedTypes[1].stringof ~ ").");
                return trustedGet!(AllowedTypes[1]);
            }

            /// ditto
            @property auto ref inout(AllowedTypes[1]) get()(auto ref inout(AllowedTypes[1]) fallback) inout
            {
                return isNull ? fallback : get();
            }

        }
    }

    /// Zero cost always nothrow `get` alternative
    auto ref trustedGet(R : Algebraic!(retId, RetTypeSets), uint retId, RetTypeSets, this This)() return @property
        if (allSatisfy!(Contains!AllowedTypes, Algebraic!(retId, RetTypeSets).AllowedTypes))
    {
        static if (_setId == retId && is(RetTypeSets == _TypeSets))
            return this;
        else
        {
            import std.meta: staticIndexOf;
            import std.traits: CopyTypeQualifiers;
            alias RhsAllowedTypes = Algebraic!(retId, RetTypeSets).AllowedTypes;
            alias Ret = CopyTypeQualifiers!(This, Algebraic!(retId, RetTypeSets));
            // uint rhsTypeId;
            switch (_storage.id)
            {
                foreach (i, T; AllowedTypes)
                static if (staticIndexOf!(T, RhsAllowedTypes) >= 0)
                {
                    case i:
                        static if (is(T == void))
                            return (()@trusted => cast(Ret) Ret._void)();
                        else
                            return Ret(trustedGet!T);
                }
                default:
                    assert(0, variantMemberExceptionMsg);
            }
            return ret;
        }
    }

    /++
    Throws: Exception if the storage contains value of the type that isn't represented in the allowed type set of the requested algebraic.
    +/
    auto ref get(R : Algebraic!(retId, RetTypeSets), uint retId, RetTypeSets, this This)() return @property
        if (allSatisfy!(Contains!AllowedTypes, Algebraic!(retId, RetTypeSets).AllowedTypes))
    {
        static if (_setId == retId && is(RetTypeSets == _TypeSets))
            return this;
        else
        {
            import std.meta: staticIndexOf;
            import std.traits: CopyTypeQualifiers;
            alias RhsAllowedTypes = Algebraic!(retId, RetTypeSets).AllowedTypes;
            alias Ret = CopyTypeQualifiers!(This, Algebraic!(retId, RetTypeSets));
            // uint rhsTypeId;
            switch (_storage.id)
            {
                foreach (i, T; AllowedTypes)
                static if (staticIndexOf!(T, RhsAllowedTypes) >= 0)
                {
                    case i:
                        static if (is(T == void))
                            return (()@trusted => cast(Ret) Ret._void)();
                        else
                            return Ret(trustedGet!T);
                }
                default:
                    throw variantMemberException;
            }
            return ret;
        }
    }

    static foreach (i, T; AllowedTypes)
    {
        private auto ref _mutableTrustedGet(E)() @trusted @property return const nothrow
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
                    throw variantException;
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

// const propogation
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

// ditto
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
alias visit(visitors...) = visitImpl!(naryFun!visitors, Exhaustive.compileTime, false);

///
@safe pure @nogc nothrow
version(mir_core_test) unittest
{
    alias Number = Variant!(int, double);

    Number x = 23;
    Number y = 1.0;

    assert(x.visit!((int v) => true, (float v) => false));
    assert(y.visit!((int v) => false, (float v) => true));
}

///
@safe pure @nogc
version(mir_core_test) unittest
{
    alias Number = Nullable!(int, double);

    Number z = null; // default
    Number x = 23;
    Number y = 1.0;

    () nothrow {
        assert(x.visit!((int v) => true, (float v) => false));
        assert(y.visit!((int v) => false, (v) => true));
        assert(z.visit!((typeof(null) v) => true, (v) => false));
    } ();

    auto xx = x.get;
    static assert (is(typeof(xx) == Variant!(int, double)));
    assert(xx.visit!((int v) => v, (float v) => 0) == 23);
    assert(xx.visit!((ref v) => v) == 23);

    x = null;
    y.nullify;

    assert(x.isNull);
    assert(y.isNull);
    assert(z.isNull);
    assert(z == y);
}

/++
Checks $(LREF .Algebraic.toString) and `void`
$(LREF Algerbraic)`.toString` requries `mir-algorithm` package
+/
@safe pure nothrow version(mir_core_test) unittest
{
    import mir.conv: to;
    enum MIR_ALGORITHM = __traits(compiles, { import mir.format; });

    alias visitorHandler = visit!(
        (typeof(null)) => "NULL",
        () => "VOID",
        (ref r) {r += 1;}, // returns void
    );

    alias secondOrderVisitorHandler = visit!(
        () => "SO VOID", // void => to "RV VOID"
        (str) => str, // string to => it self
    );

    alias V = Nullable!(void, int);
    static assert(is(V == Variant!(typeof(null), void, int)));

    V variant;

    assert(secondOrderVisitorHandler(visitorHandler(variant)) == "NULL");
    assert(variant.to!string == "null");

    variant = V._void;
    assert(variant._is!void);
    assert(is(typeof(variant.get!void()) == void));

    assert(secondOrderVisitorHandler(visitorHandler(variant)) == "VOID");
    assert(variant.to!string == "void");

    variant = 5;

    assert(secondOrderVisitorHandler(visitorHandler(variant)) == "SO VOID");
    assert(variant == 6);
    assert(variant.to!string == (MIR_ALGORITHM ? "6" : "int"));
}

/++
Behaves as $(LREF visit) but doesn't enforce at compile time that all types can be handled by the visiting functions.
Throws: Exception if `naryFun!visitors` can't be called with provided arguments
+/
alias tryVisit(visitors...) = visitImpl!(naryFun!visitors, Exhaustive.exception, false);

///
@safe pure @nogc
version(mir_core_test) unittest
{
    alias Number = Variant!(int, double);

    Number x = 23;

    assert(x.tryVisit!((int v) => true));
}

/++
Behaves as $(LREF visit) but doesn't enforce at compile time that all types can be handled by the visiting functions.
Returns: nullable variant, null value is used if `naryFun!visitors` can't be called with provided arguments.
+/
alias optionalVisit(visitors...) = visitImpl!(naryFun!visitors, Exhaustive.nullable, false);

///
@safe pure @nogc nothrow
version(mir_core_test) unittest
{
    static struct S { int a; }

    Variant!(S, double) variant;

    alias optionalVisitInst = optionalVisit!((ref value) => value + 0);

    // do nothing because of variant isn't initialized
    Nullable!double result = optionalVisitInst(variant);
    assert(result.isNull);

    variant = S(2);
    // do nothing because of lambda can't compile
    result = optionalVisitInst(variant);
    assert(result == null);

    variant = 3.0;
    result = optionalVisitInst(variant);
    assert (result == 3.0);
}

/++
Behaves as $(LREF visit) but doesn't enforce at compile time that all types can be handled by the visiting functions.
Returns: optionally nullable type, null value is used if `naryFun!visitors` can't be called with provided arguments.
+/
alias autoVisit(visitors...) = visitImpl!(naryFun!visitors, Exhaustive.auto_, false);


/++
Applies a delegate or function to the given arguments depending on the held type,
ensuring that all types are handled by the visiting functions.

The handler supports multiple dispatch or multimethods: a feature of handler in which
a function or method can be dynamically dispatched based on the run time (dynamic) type or,
in the more general case, some other attribute of more than one of its arguments.

See_also: $(HTTPS en.wikipedia.org/wiki/Multiple_dispatch, Multiple dispatch)
+/
alias match(visitors...) = visitImpl!(naryFun!visitors, Exhaustive.compileTime, true);

///
unittest
{
    struct Asteroid { uint size; }
    struct Spaceship { uint size; }
    alias SpaceObject = Variant!(Asteroid, Spaceship);

    alias collideWith = match!(
        (Asteroid x, Asteroid y) => "a/a",
        (Asteroid x, Spaceship y) => "a/s",
        (Spaceship x, Asteroid y) => "s/a",
        (Spaceship x, Spaceship y) => "s/s",
    );

    import mir.utility: min;
    alias oops = match!((a, b) => (a.size + b.size) > 3 && min(a.size, b.size) > 1);

    alias collide = (x, y) => oops(x, y) ? "big-boom" : collideWith(x, y);

    auto ea = Asteroid(1);
    auto es = Spaceship(2);
    auto oa = SpaceObject(ea);
    auto os = SpaceObject(es);

    // Asteroid-Asteroid
    assert(collide(ea, ea) == "a/a");
    assert(collide(ea, oa) == "a/a");
    assert(collide(oa, ea) == "a/a");
    assert(collide(oa, oa) == "a/a");

    // Asteroid-Spaceship
    assert(collide(ea, es) == "a/s");
    assert(collide(ea, os) == "a/s");
    assert(collide(oa, es) == "a/s");
    assert(collide(oa, os) == "a/s");

    // Spaceship-Asteroid
    assert(collide(es, ea) == "s/a");
    assert(collide(es, oa) == "s/a");
    assert(collide(os, ea) == "s/a");
    assert(collide(os, oa) == "s/a");

    // Spaceship-Spaceship
    assert(collide(es, es) == "big-boom");
    assert(collide(es, os) == "big-boom");
    assert(collide(os, es) == "big-boom");
    assert(collide(os, os) == "big-boom");
}

/++
Behaves as $(LREF match) but doesn't enforce at compile time that all types can be handled by the visiting functions.
Throws: Exception if `naryFun!visitors` can't be called with provided arguments
+/
alias tryMatch(visitors...) = visitImpl!(naryFun!visitors, Exhaustive.exception, true);

///
unittest
{
    import std.exception: assertThrown;
    struct Asteroid { uint size; }
    struct Spaceship { uint size; }
    alias SpaceObject = Variant!(Asteroid, Spaceship);

    alias collideWith = tryMatch!(
        (Asteroid x, Asteroid y) => "a/a",
        // No visitor for A/S pair 
        // (Asteroid x, Spaceship y) => "a/s",
        (Spaceship x, Asteroid y) => "s/a",
        (Spaceship x, Spaceship y) => "s/s",
    );

    import mir.utility: min;
    alias oops = match!((a, b) => (a.size + b.size) > 3 && min(a.size, b.size) > 1);

    alias collide = (x, y) => oops(x, y) ? "big-boom" : collideWith(x, y);

    auto ea = Asteroid(1);
    auto es = Spaceship(2);
    auto oa = SpaceObject(ea);
    auto os = SpaceObject(es);

    // Asteroid-Asteroid
    assert(collide(ea, ea) == "a/a");
    assert(collide(ea, oa) == "a/a");
    assert(collide(oa, ea) == "a/a");
    assert(collide(oa, oa) == "a/a");

    // Asteroid-Spaceship
    assertThrown!Exception(collide(ea, es));
    assertThrown!Exception(collide(ea, os));
    assertThrown!Exception(collide(oa, es));
    assertThrown!Exception(collide(oa, os));

     // not enough information to deduce the type from (ea, es) pair
    static assert(is(typeof(collide(ea, es)) == void));
    // can deduce the type based on other return values
    static assert(is(typeof(collide(ea, os)) == string));
    static assert(is(typeof(collide(oa, es)) == string));
    static assert(is(typeof(collide(oa, os)) == string));

    // Spaceship-Asteroid
    assert(collide(es, ea) == "s/a");
    assert(collide(es, oa) == "s/a");
    assert(collide(os, ea) == "s/a");
    assert(collide(os, oa) == "s/a");

    // Spaceship-Spaceship
    assert(collide(es, es) == "big-boom");
    assert(collide(es, os) == "big-boom");
    assert(collide(os, es) == "big-boom");
    assert(collide(os, os) == "big-boom");
}

/++
Behaves as $(LREF match) but doesn't enforce at compile time that all types can be handled by the visiting functions.
Returns: nullable variant, null value is used if `naryFun!visitors` can't be called with provided arguments.
+/
alias optionalMatch(visitors...) = visitImpl!(naryFun!visitors, Exhaustive.nullable, true);

///
unittest
{
    struct Asteroid { uint size; }
    struct Spaceship { uint size; }
    alias SpaceObject = Variant!(Asteroid, Spaceship);

    alias collideWith = optionalMatch!(
        (Asteroid x, Asteroid y) => "a/a",
        // No visitor for A/S pair 
        // (Asteroid x, Spaceship y) => "a/s",
        (Spaceship x, Asteroid y) => "s/a",
        (Spaceship x, Spaceship y) => "s/s",
    );

    import mir.utility: min;
    alias oops = match!((a, b) => (a.size + b.size) > 3 && min(a.size, b.size) > 1);

    alias collide = (x, y) => oops(x, y) ? Nullable!string("big-boom") : collideWith(x, y);

    auto ea = Asteroid(1);
    auto es = Spaceship(2);
    auto oa = SpaceObject(ea);
    auto os = SpaceObject(es);

    // Asteroid-Asteroid
    assert(collide(ea, ea) == "a/a");
    assert(collide(ea, oa) == "a/a");
    assert(collide(oa, ea) == "a/a");
    assert(collide(oa, oa) == "a/a");

    // Asteroid-Spaceship
    // assert(collide(ea, es).isNull);  // Compiler error: incompatible types
    assert(collideWith(ea, es).isNull); // OK
    assert(collide(ea, os).isNull);
    assert(collide(oa, es).isNull);
    assert(collide(oa, os).isNull);


    // Spaceship-Asteroid
    assert(collide(es, ea) == "s/a");
    assert(collide(es, oa) == "s/a");
    assert(collide(os, ea) == "s/a");
    assert(collide(os, oa) == "s/a");

    // Spaceship-Spaceship
    assert(collide(es, es) == "big-boom");
    assert(collide(es, os) == "big-boom");
    assert(collide(os, es) == "big-boom");
    assert(collide(os, os) == "big-boom");

    // check types  

    static assert(!__traits(compiles, collide(Asteroid.init, Spaceship.init)));
    static assert(is(typeof(collideWith(Asteroid.init, Spaceship.init)) == Nullable!()));

    static assert(is(typeof(collide(Asteroid.init, Asteroid.init)) == Nullable!string));
    static assert(is(typeof(collide(Asteroid.init, SpaceObject.init)) == Nullable!string));
    static assert(is(typeof(collide(SpaceObject.init, Asteroid.init)) == Nullable!string));
    static assert(is(typeof(collide(SpaceObject.init, SpaceObject.init)) == Nullable!string));
    static assert(is(typeof(collide(SpaceObject.init, Spaceship.init)) == Nullable!string));
    static assert(is(typeof(collide(Spaceship.init, Asteroid.init)) == Nullable!string));
    static assert(is(typeof(collide(Spaceship.init, SpaceObject.init)) == Nullable!string));
    static assert(is(typeof(collide(Spaceship.init, Spaceship.init)) == Nullable!string));
}

/++
Behaves as $(LREF match) but doesn't enforce at compile time that all types can be handled by the visiting functions.
Returns: optionally nullable type, null value is used if `naryFun!visitors` can't be called with provided arguments.
+/
alias autoMatch(visitors...) = visitImpl!(naryFun!visitors, Exhaustive.auto_, true);

///
unittest
{
    struct Asteroid { uint size; }
    struct Spaceship { uint size; }
    alias SpaceObject = Variant!(Asteroid, Spaceship);

    alias collideWith = autoMatch!(
        (Asteroid x, Asteroid y) => "a/a",
        // No visitor for A/S pair 
        // (Asteroid x, Spaceship y) => "a/s",
        (Spaceship x, Asteroid y) => "s/a",
        (Spaceship x, Spaceship y) => "s/s",
    );

    import mir.utility: min;
    alias oops = match!((a, b) => (a.size + b.size) > 3 && min(a.size, b.size) > 1);

    import mir.conv: to;
    alias collide = (x, y) => oops(x, y) ? "big-boom".to!(typeof(collideWith(x, y))) : collideWith(x, y);

    auto ea = Asteroid(1);
    auto es = Spaceship(2);
    auto oa = SpaceObject(ea);
    auto os = SpaceObject(es);

    // Asteroid-Asteroid
    assert(collide(ea, ea) == "a/a");
    assert(collide(ea, oa) == "a/a");
    assert(collide(oa, ea) == "a/a");
    assert(collide(oa, oa) == "a/a");

    // Asteroid-Spaceship
    // assert(collide(ea, es).isNull);  // Compiler error: incompatible types
    assert(collideWith(ea, es).isNull); // OK
    assert(collide(ea, os).isNull);
    assert(collide(oa, es).isNull);
    assert(collide(oa, os).isNull);

    // Spaceship-Asteroid
    assert(collide(es, ea) == "s/a");
    assert(collide(es, oa) == "s/a");
    assert(collide(os, ea) == "s/a");
    assert(collide(os, oa) == "s/a");

    // Spaceship-Spaceship
    assert(collide(es, es) == "big-boom");
    assert(collide(es, os) == "big-boom");
    assert(collide(os, es) == "big-boom");
    assert(collide(os, os) == "big-boom");

    // check types  

    static assert(!__traits(compiles, collide(Asteroid.init, Spaceship.init)));
    static assert(is(typeof(collideWith(Asteroid.init, Spaceship.init)) == Nullable!()));

    static assert(is(typeof(collide(Asteroid.init, Asteroid.init)) == string));
    static assert(is(typeof(collide(SpaceObject.init, Asteroid.init)) == string));
    static assert(is(typeof(collide(Spaceship.init, Asteroid.init)) == string));
    static assert(is(typeof(collide(Spaceship.init, SpaceObject.init)) == string));
    static assert(is(typeof(collide(Spaceship.init, Spaceship.init)) == string));

    static assert(is(typeof(collide(Asteroid.init, SpaceObject.init)) == Nullable!string));
    static assert(is(typeof(collide(SpaceObject.init, SpaceObject.init)) == Nullable!string));
    static assert(is(typeof(collide(SpaceObject.init, Spaceship.init)) == Nullable!string));
}

/++
Applies a member handler to the given Variant depending on the held type,
ensuring that all types are handled by the visiting handler.
+/
alias getMember(string member) = visitImpl!(getMemberHandler!member, Exhaustive.compileTime, false);

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
Behaves as $(LREF getMember) but doesn't enforce at compile time that all types can be handled by the member visitor.
Throws: Exception if member can't be accessed with provided arguments
+/
alias tryGetMember(string member) = visitImpl!(getMemberHandler!member, Exhaustive.exception, false);

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

    assert(x.visit!((int v) => true, (float v) => false));
    assert(y.visit!((int v) => false, (float v) => true));
}

/++
Behaves as $(LREF getMember) but doesn't enforce at compile time that all types can be handled by the member visitor.
Returns: nullable variant, null value is used if the member can't be called with provided arguments.
+/
alias optionalGetMember(string member) = visitImpl!(getMemberHandler!member, Exhaustive.nullable, false);

/++
Behaves as $(LREF getMember) but doesn't enforce at compile time that all types can be handled by the member visitor.
Returns: optionally nullable type, null value is used if the member can't be called with provided arguments.
+/
alias autoGetMember(string member) = visitImpl!(getMemberHandler!member, Exhaustive.auto_, false);

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
    import std.meta: staticMap;

    alias VariantReturnTypes = NoDuplicates!(staticMap!(TryRemoveConst, T));
}

private enum Exhaustive
{
    compileTime,
    exception,
    nullable,
    auto_,
}

private template nextVisitor(T, alias visitor, alias arg)
{
    static if (is(T == void))
    {
        alias nextVisitor = visitor;
    }
    else
    auto ref nextVisitor(NextArgs...)(auto ref NextArgs nextArgs)
    {
        import core.lifetime: forward;
        return visitor(arg.trustedGet!T, forward!nextArgs);
    }
}

private template nextVisitor(alias visitor, alias arg)
{
    auto ref nextVisitor(NextArgs...)(auto ref NextArgs nextArgs)
    {
        import core.lifetime: forward;
        return visitor(arg, forward!nextArgs);
    }
}

private template visitThis(alias visitor, Exhaustive nextExhaustive, args...)
{
    auto ref visitThis(T)()
    {
        import core.lifetime: forward;
        return .visitImpl!(nextVisitor!(T, visitor, args[0]), nextExhaustive, true)(forward!(args[1 .. $]));
    }
}

private template visitLast(alias visitor, args...)
{
    auto ref visitLast(T)()
    {
        import core.lifetime: forward;
        static if (is(T == void))
            return visitor(forward!(args[1 .. $]));
        else
            return visitor(args[0].trustedGet!T, forward!(args[1 .. $]));
    }
}

private template visitImpl(alias visitor, Exhaustive exhaustive, bool fused)
{
    import std.meta: anySatisfy, staticMap, AliasSeq;

    ///
    auto ref visitImpl(Args...)(auto ref Args args)
    {
        import core.lifetime: forward;

        static if (!anySatisfy!(isVariant, Args))
        {
            static if (exhaustive == Exhaustive.compileTime)
            {
                return visitor(forward!args);
            }
            else
            static if (exhaustive == Exhaustive.exception)
            {
                static if (__traits(compiles, visitor(forward!args)))
                    return visitor(forward!args);
                else
                    throw variantMemberException;
            }
            else
            static if (exhaustive == Exhaustive.nullable)
            {
                static if (__traits(compiles, visitor(forward!args)))
                    return Nullable!(typeof(visitor(forward!args)))(visitor(forward!args));
                else
                    return Nullable!().init;
            }
            else
            static if (exhaustive == Exhaustive.auto_)
            {
                static if (__traits(compiles, visitor(forward!args)))
                    return visitor(forward!args);
                else
                    return Nullable!().init;
            }
            else
            static assert(0, "not implemented");
        }
        else
        static if (!isVariant!(Args[0]))
        {
            return .visitImpl!(nextVisitor!(visitor, args[0]), exhaustive, fused)(forward!(args[1 .. $]));
        }
        else
        {
            static if (fused && anySatisfy!(isVariant, Args[1 .. $]))
            {
                alias fun = visitThis!(visitor, exhaustive, args);
            }
            else
            {
                static assert (isVariant!(Args[0]), "First argument should be a Mir Algebraic type");
                alias fun = visitLast!(visitor, args);
            }

            template VariantReturnTypesImpl(T)
            {
                static if (__traits(compiles, fun!T()))
                    static if (fused && is(typeof(fun!T()) : Algebraic!(id, TypeSets), uint id, TypeSets...))
                        alias VariantReturnTypesImpl = TryRemoveConst!(typeof(fun!T())).AllowedTypes;
                    else
                    alias VariantReturnTypesImpl = AliasSeq!(TryRemoveConst!(typeof(fun!T())));
                else
                static if (exhaustive == Exhaustive.auto_)
                    alias VariantReturnTypesImpl = AliasSeq!(typeof(null));
                else
                    alias VariantReturnTypesImpl = AliasSeq!();
            }

            static if (exhaustive == Exhaustive.nullable)
                alias AllReturnTypes = NoDuplicates!(typeof(null), staticMap!(VariantReturnTypesImpl, Args[0].AllowedTypes));
            else
                alias AllReturnTypes = NoDuplicates!(staticMap!(VariantReturnTypesImpl, Args[0].AllowedTypes));

            switch (args[0]._storage.id)
            {
                static foreach (i, T; Args[0].AllowedTypes)
                {
                    case i:
                        static if (__traits(compiles, fun!T()))
                        {
                            static if (AllReturnTypes.length == 1)
                            {
                                return fun!T();
                            }
                            else
                            static if (is(VariantReturnTypesImpl!T == AliasSeq!void))
                            {
                                fun!T();
                                return Variant!AllReturnTypes._void;
                            }
                            else
                            static if (is(typeof(fun!T()) : Variant!AllReturnTypes))
                            {
                                return fun!T();
                            }
                            else
                            {
                                return Variant!AllReturnTypes(fun!T());
                            }
                        }
                        else
                        static if (exhaustive == Exhaustive.compileTime)
                        {
                            static if (is(T == typeof(null)))
                                assert(0, "Null " ~ Args[0].stringof);
                            else
                                static assert(0, Args[0].stringof ~ ": the visitor cann't be caled with arguments " ~ Args.stringof);
                        }
                        else
                        static if (exhaustive == Exhaustive.nullable || exhaustive == Exhaustive.auto_)
                        {
                            return Variant!AllReturnTypes(null);
                        }
                        else
                        {
                            throw variantMemberException;
                        }
                }
                default: assert(0);
            }
        }
    }
}

@safe pure @nogc
version(mir_core_test) unittest
{
    static struct S { int a; }

    Variant!(S, double) variant;
    variant = 1.0;
    variant.tryVisit!((ref value, b) => value += b)(2);
    assert (variant.get!double == 3);

    alias fun = (ref value) {
        static if (is(typeof(value) == S))
            value.a += 2;
        else
           value += 2;
    };

    variant.tryVisit!fun;
    assert (variant.get!double == 5);

    variant = S(4);
    variant.tryVisit!fun;
    assert (variant.get!S.a == 6);
}

@safe pure @nogc
version(mir_core_test) unittest
{

    static struct PODWithLongPointer {
        long* x;
        this(long l) pure
        {
            x = new long(l);
        }

    @property:
        long a() const {
            return x ? *x : 0;
        }

        void a(long l) {
            if (x) {
                *x = l;
            } else {
                x = new long(l);
            }
        }
    }
    import std.traits: TemplateArgsOf;
    static assert(is(TemplateArgsOf!(TypeSet!(byte, immutable PODWithLongPointer)) == AliasSeq!(byte, immutable PODWithLongPointer)));
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
// END OF MIR ALGEBRIAC /////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

private:

import std.meta: AliasSeq, staticMap;

template Erase(T, TList...)
{
    alias Erase = GenericErase!(T, TList).result;
}

template Erase(alias T, TList...)
{
    alias Erase = GenericErase!(T, TList).result;
}

template GenericErase(args...)
if (args.length >= 1)
{
    alias e     = OldAlias!(args[0]);
    alias tuple = args[1 .. $] ;

    static if (tuple.length)
    {
        alias head = OldAlias!(tuple[0]);
        alias tail = tuple[1 .. $];

        static if (isSame!(e, head))
            alias result = tail;
        else
            alias result = AliasSeq!(head, GenericErase!(e, tail).result);
    }
    else
    {
        alias result = AliasSeq!();
    }
}

template Pack(T...)
{
    alias Expand = T;
    enum equals(U...) = isSame!(Pack!T, Pack!U);
}


template EraseAll(T, TList...)
{
    alias EraseAll = GenericEraseAll!(T, TList).result;
}

template EraseAll(alias T, TList...)
{
    alias EraseAll = GenericEraseAll!(T, TList).result;
}

template GenericEraseAll(args...)
if (args.length >= 1)
{
    alias e     = OldAlias!(args[0]);
    alias tuple = args[1 .. $];

    static if (tuple.length)
    {
        alias head = OldAlias!(tuple[0]);
        alias tail = tuple[1 .. $];
        alias next = AliasSeq!(
            GenericEraseAll!(e, tail[0..$/2]).result,
            GenericEraseAll!(e, tail[$/2..$]).result
            );

        static if (isSame!(e, head))
            alias result = next;
        else
            alias result = AliasSeq!(head, next);
    }
    else
    {
        alias result = AliasSeq!();
    }
}

template OldAlias(T)
{
    alias OldAlias = T;
}

template EraseAllN(uint N, TList...)
{
    static if (N == 1)
    {
        alias EraseAllN = EraseAll!(TList[0], TList[1 .. $]);
    }
    else
    {
        static if (N & 1)
            alias EraseAllN = EraseAllN!(N / 2, TList[N / 2 + 1 .. N],
                    EraseAllN!(N / 2 + 1, TList[0 .. N / 2 + 1], TList[N .. $]));
        else
            alias EraseAllN = EraseAllN!(N / 2, TList[N / 2 .. N],
                    EraseAllN!(N / 2, TList[0 .. N / 2], TList[N .. $]));
    }
}

template NoDuplicates(TList...)
{
    static if (TList.length >= 2)
    {
        alias fst = NoDuplicates!(TList[0 .. $/2]);
        alias snd = NoDuplicates!(TList[$/2 .. $]);
        alias NoDuplicates = AliasSeq!(fst, EraseAllN!(fst.length, fst, snd));
    }
    else
    {
        alias NoDuplicates = TList;
    }
}


template isSame(ab...)
if (ab.length == 2)
{
    static if (is(ab[0]) && is(ab[1]))
    {
        enum isSame = is(ab[0] == ab[1]);
    }
    else static if (!is(ab[0]) && !is(ab[1]) &&
                    !(is(typeof(&ab[0])) && is(typeof(&ab[1]))) &&
                     __traits(compiles, { enum isSame = ab[0] == ab[1]; }))
    {
        enum isSame = (ab[0] == ab[1]);
    }
    else
    {
        enum isSame = __traits(isSame, ab[0], ab[1]);
    }
}

template Mod(From, To)
{
    template Mod(T)
    {
        static if (is(T == From))
            alias Mod = To;
        else
            alias Mod = T;
    }
}

template Replace(From, To, T...)
{
    alias Replace = staticMap!(Mod!(From, To), T);
}

template ReplaceTypeUnless(alias pred, From, To, T...)
{
    static if (T.length == 1)
    {
        static if (pred!(T[0]))
            alias ReplaceTypeUnless = T[0];
        else static if (is(T[0] == From))
            alias ReplaceTypeUnless = To;
        else static if (is(T[0] == const(U), U))
            alias ReplaceTypeUnless = const(ReplaceTypeUnless!(pred, From, To, U));
        else static if (is(T[0] == immutable(U), U))
            alias ReplaceTypeUnless = immutable(ReplaceTypeUnless!(pred, From, To, U));
        else static if (is(T[0] == shared(U), U))
            alias ReplaceTypeUnless = shared(ReplaceTypeUnless!(pred, From, To, U));
        else static if (is(T[0] == U*, U))
        {
            static if (is(U == function))
                alias ReplaceTypeUnless = replaceTypeInFunctionTypeUnless!(pred, From, To, T[0]);
            else
                alias ReplaceTypeUnless = ReplaceTypeUnless!(pred, From, To, U)*;
        }
        else static if (is(T[0] == delegate))
        {
            alias ReplaceTypeUnless = replaceTypeInFunctionTypeUnless!(pred, From, To, T[0]);
        }
        else static if (is(T[0] == function))
        {
            static assert(0, "Function types not supported," ~
                " use a function pointer type instead of " ~ T[0].stringof);
        }
        else static if (is(T[0] == U!V, alias U, V...))
        {
            template replaceTemplateArgs(T...)
            {
                static if (is(typeof(T[0])))
                    static if (__traits(compiles, {alias replaceTemplateArgs = T[0];}))
                        alias replaceTemplateArgs = T[0];
                    else
                        enum replaceTemplateArgs = T[0];
                else
                    alias replaceTemplateArgs = ReplaceTypeUnless!(pred, From, To, T[0]);
            }
            alias ReplaceTypeUnless = U!(staticMap!(replaceTemplateArgs, V));
        }
        else static if (is(T[0] == struct))
            // don't match with alias this struct below
            // https://issues.dlang.org/show_bug.cgi?id=15168
            alias ReplaceTypeUnless = T[0];
        else static if (is(T[0] == U[], U))
            alias ReplaceTypeUnless = ReplaceTypeUnless!(pred, From, To, U)[];
        else static if (is(T[0] == U[n], U, size_t n))
            alias ReplaceTypeUnless = ReplaceTypeUnless!(pred, From, To, U)[n];
        else static if (is(T[0] == U[V], U, V))
            alias ReplaceTypeUnless =
                ReplaceTypeUnless!(pred, From, To, U)[ReplaceTypeUnless!(pred, From, To, V)];
        else
            alias ReplaceTypeUnless = T[0];
    }
    else static if (T.length > 1)
    {
        alias ReplaceTypeUnless = AliasSeq!(ReplaceTypeUnless!(pred, From, To, T[0]),
            ReplaceTypeUnless!(pred, From, To, T[1 .. $]));
    }
    else
    {
        alias ReplaceTypeUnless = AliasSeq!();
    }
}

@safe version(mir_core_test) unittest
{
    import std.typecons: Tuple;
    import std.traits : isArray;
    static assert(
        is(ReplaceTypeUnless!(isArray, int, string, int*) == string*) &&
        is(ReplaceTypeUnless!(isArray, int, string, int[]) == int[]) &&
        is(ReplaceTypeUnless!(isArray, int, string, Tuple!(int, int[]))
            == Tuple!(string, int[]))
   );
}

template Contains(Types...)
{
    import std.meta: staticIndexOf;
    enum Contains(T) = staticIndexOf!(T, Types) >= 0;
}

template replaceTypeInFunctionTypeUnless(alias pred, From, To, fun)
{
    import std.meta;
    import std.traits;
    alias RX = ReplaceTypeUnless!(pred, From, To, ReturnType!fun);
    alias PX = AliasSeq!(ReplaceTypeUnless!(pred, From, To, Parameters!fun));
    // Wrapping with AliasSeq is neccesary because ReplaceType doesn't return
    // tuple if Parameters!fun.length == 1
    string gen()
    {
        enum  linkage = functionLinkage!fun;
        alias attributes = functionAttributes!fun;
        enum  variadicStyle = variadicFunctionStyle!fun;
        alias storageClasses = ParameterStorageClassTuple!fun;
        string result;
        result ~= "extern(" ~ linkage ~ ") ";
        static if (attributes & FunctionAttribute.ref_)
        {
            result ~= "ref ";
        }
        result ~= "RX";
        static if (is(fun == delegate))
            result ~= " delegate";
        else
            result ~= " function";
        result ~= "(";
        static foreach (i; 0 .. PX.length)
        {
            if (i)
                result ~= ", ";
            if (storageClasses[i] & ParameterStorageClass.scope_)
                result ~= "scope ";
            if (storageClasses[i] & ParameterStorageClass.out_)
                result ~= "out ";
            if (storageClasses[i] & ParameterStorageClass.ref_)
                result ~= "ref ";
            if (storageClasses[i] & ParameterStorageClass.lazy_)
                result ~= "lazy ";
            if (storageClasses[i] & ParameterStorageClass.return_)
                result ~= "return ";
            result ~= "PX[" ~ i.stringof ~ "]";
        }
        static if (variadicStyle == Variadic.typesafe)
            result ~= " ...";
        else static if (variadicStyle != Variadic.no)
            result ~= ", ...";
        result ~= ")";
        static if (attributes & FunctionAttribute.pure_)
            result ~= " pure";
        static if (attributes & FunctionAttribute.nothrow_)
            result ~= " nothrow";
        static if (attributes & FunctionAttribute.property)
            result ~= " @property";
        static if (attributes & FunctionAttribute.trusted)
            result ~= " @trusted";
        static if (attributes & FunctionAttribute.safe)
            result ~= " @safe";
        static if (attributes & FunctionAttribute.nogc)
            result ~= " @nogc";
        static if (attributes & FunctionAttribute.system)
            result ~= " @system";
        static if (attributes & FunctionAttribute.const_)
            result ~= " const";
        static if (attributes & FunctionAttribute.immutable_)
            result ~= " immutable";
        static if (attributes & FunctionAttribute.inout_)
            result ~= " inout";
        static if (attributes & FunctionAttribute.shared_)
            result ~= " shared";
        static if (attributes & FunctionAttribute.return_)
            result ~= " return";
        return result;
    }
    mixin("alias replaceTypeInFunctionTypeUnless = " ~ gen() ~ ";");
}

enum false_(T) = false;

alias ReplaceType(From, To, T...) = ReplaceTypeUnless!(false_, From, To, T);

version(mir_core_test) @safe unittest
{
    import std.typecons: Unique, Tuple;
    template Test(Ts...)
    {
        static if (Ts.length)
        {
            //pragma(msg, "Testing: ReplaceType!("~Ts[0].stringof~", "
            //    ~Ts[1].stringof~", "~Ts[2].stringof~")");
            static assert(is(ReplaceType!(Ts[0], Ts[1], Ts[2]) == Ts[3]),
                "ReplaceType!("~Ts[0].stringof~", "~Ts[1].stringof~", "
                    ~Ts[2].stringof~") == "
                    ~ReplaceType!(Ts[0], Ts[1], Ts[2]).stringof);
            alias Test = Test!(Ts[4 .. $]);
        }
        else alias Test = void;
    }
    //import core.stdc.stdio;
    alias RefFun1 = ref int function(float, long);
    alias RefFun2 = ref float function(float, long);
    extern(C) int printf(const char*, ...) nothrow @nogc @system;
    extern(C) float floatPrintf(const char*, ...) nothrow @nogc @system;
    int func(float);
    int x;
    struct S1 { void foo() { x = 1; } }
    struct S2 { void bar() { x = 2; } }
    alias Pass = Test!(
        int, float, typeof(&func), float delegate(float),
        int, float, typeof(&printf), typeof(&floatPrintf),
        int, float, int function(out long, ...),
            float function(out long, ...),
        int, float, int function(ref float, long),
            float function(ref float, long),
        int, float, int function(ref int, long),
            float function(ref float, long),
        int, float, int function(out int, long),
            float function(out float, long),
        int, float, int function(lazy int, long),
            float function(lazy float, long),
        int, float, int function(out long, ref const int),
            float function(out long, ref const float),
        int, int, int, int,
        int, float, int, float,
        int, float, const int, const float,
        int, float, immutable int, immutable float,
        int, float, shared int, shared float,
        int, float, int*, float*,
        int, float, const(int)*, const(float)*,
        int, float, const(int*), const(float*),
        const(int)*, float, const(int*), const(float),
        int*, float, const(int)*, const(int)*,
        int, float, int[], float[],
        int, float, int[42], float[42],
        int, float, const(int)[42], const(float)[42],
        int, float, const(int[42]), const(float[42]),
        int, float, int[int], float[float],
        int, float, int[double], float[double],
        int, float, double[int], double[float],
        int, float, int function(float, long), float function(float, long),
        int, float, int function(float), float function(float),
        int, float, int function(float, int), float function(float, float),
        int, float, int delegate(float, long), float delegate(float, long),
        int, float, int delegate(float), float delegate(float),
        int, float, int delegate(float, int), float delegate(float, float),
        int, float, Unique!int, Unique!float,
        int, float, Tuple!(float, int), Tuple!(float, float),
        int, float, RefFun1, RefFun2,
        S1, S2,
            S1[1][][S1]* function(),
            S2[1][][S2]* function(),
        int, string,
               int[3] function(   int[] arr,    int[2] ...) pure @trusted,
            string[3] function(string[] arr, string[2] ...) pure @trusted,
    );
    // https://issues.dlang.org/show_bug.cgi?id=15168
    static struct T1 { string s; alias s this; }
    static struct T2 { char[10] s; alias s this; }
    static struct T3 { string[string] s; alias s this; }
    alias Pass2 = Test!(
        ubyte, ubyte, T1, T1,
        ubyte, ubyte, T2, T2,
        ubyte, ubyte, T3, T3,
    );
}
// https://issues.dlang.org/show_bug.cgi?id=17116
version(mir_core_test) @safe unittest
{
    alias ConstDg = void delegate(float) const;
    alias B = void delegate(int) const;
    alias A = ReplaceType!(float, int, ConstDg);
    static assert(is(B == A));
}
 // https://issues.dlang.org/show_bug.cgi?id=19696
version(mir_core_test) @safe unittest
{
    static struct T(U) {}
    static struct S { T!int t; alias t this; }
    static assert(is(ReplaceType!(float, float, S) == S));
}
 // https://issues.dlang.org/show_bug.cgi?id=19697
version(mir_core_test) @safe unittest
{
    class D(T) {}
    class C : D!C {}
    static assert(is(ReplaceType!(float, float, C)));
}
// https://issues.dlang.org/show_bug.cgi?id=16132
version(mir_core_test) @safe unittest
{
    interface I(T) {}
    class C : I!int {}
    static assert(is(ReplaceType!(int, string, C) == C));
}
