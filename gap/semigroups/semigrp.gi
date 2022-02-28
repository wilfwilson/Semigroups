#############################################################################
##
##  semigroups/semigrp.gi
##  Copyright (C) 2013-2022                              James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#############################################################################
## This file contains methods for finite semigroups which do not depend on
## whether they are acting or not, i.e. they should work for all semigroups.
## It is organized as follows:
##
##   1.  Helper functions
##
##   2.  Generators
##
##   3.  Semigroup/Monoid/InverseSemigroup/InverseMonoidByGenerators
##
##   4.  RegularSemigroup
##
##   5.  ClosureSemigroup/Monoid
##
##   6.  ClosureInverseSemigroup/Monoid
##
##   7.  Subsemigroups
##
##   8.  Random semigroups and elements
##
##   9.  Changing representation: AsSemigroup, AsMonoid
##
##   10. Operators
##
#############################################################################

#############################################################################
## 1. Helper functions
#############################################################################

# Returns an isomorphism from the semigroup <S> to a semigroup in <filter> by
# composing an isomorphism from <S> to a transformation semigroup <T> with an
# isomorphism from <T> to a semigroup in <filter>, i.e.  <filter> might be
# IsMaxPlusMatrixSemigroup or similar.

SEMIGROUPS.DefaultIsomorphismSemigroup := function(filter, S)
  local iso1, inv1, iso2, inv2;

  iso1 := IsomorphismTransformationSemigroup(S);
  inv1 := InverseGeneralMapping(iso1);
  iso2 := IsomorphismSemigroup(filter, Range(iso1));
  inv2 := InverseGeneralMapping(iso2);

  return MagmaIsomorphismByFunctionsNC(S,
                                       Range(iso2),
                                       x -> (x ^ iso1) ^ iso2,
                                       x -> (x ^ inv2) ^ inv1);
end;

# Returns an isomorphism from the monoid (or IsMonoidAsSemigroup) <S> to a
# monoid in <filter> by composing an isomorphism from <S> to a transformation
# monoid <T> with an isomorphism from <T> to a monoid in <filter>, i.e.
# <filter> might be IsMaxPlusMatrixMonoid or similar.

SEMIGROUPS.DefaultIsomorphismMonoid := function(filter, S)
  local iso1, inv1, iso2, inv2;

  iso1 := IsomorphismTransformationMonoid(S);
  inv1 := InverseGeneralMapping(iso1);
  iso2 := IsomorphismMonoid(filter, Range(iso1));
  inv2 := InverseGeneralMapping(iso2);

  return MagmaIsomorphismByFunctionsNC(S,
                                       Range(iso2),
                                       x -> (x ^ iso1) ^ iso2,
                                       x -> (x ^ inv2) ^ inv1);
end;

#############################################################################
## 2. Generators
#############################################################################

InstallMethod(IsGeneratorsOfInverseSemigroup,
"for a semigroup with generators",
[IsSemigroup and HasGeneratorsOfSemigroup],
function(S)
  if IsInverseActingSemigroupRep(S) then
    # There is currently no way to enter this!
    return true;
  fi;
  return IsGeneratorsOfInverseSemigroup(GeneratorsOfSemigroup(S));
end);

# TODO(later) the next method should really be in the library
InstallMethod(IsGeneratorsOfInverseSemigroup, "for a list",
[IsList], ReturnFalse);

InstallMethod(Generators, "for a semigroup",
[IsSemigroup],
function(S)

  if HasGeneratorsOfMagmaIdeal(S) then
    return GeneratorsOfMagmaIdeal(S);
  elif HasGeneratorsOfGroup(S) then
    return GeneratorsOfGroup(S);
  elif HasGeneratorsOfInverseMonoid(S) then
    return GeneratorsOfInverseMonoid(S);
  elif HasGeneratorsOfInverseSemigroup(S) then
    return GeneratorsOfInverseSemigroup(S);
  elif HasGeneratorsOfMonoid(S) then
    return GeneratorsOfMonoid(S);
  fi;

  return GeneratorsOfSemigroup(S);
end);

#############################################################################
## 3. Semigroup/Monoid/InverseSemigroup/InverseMonoidByGenerators
#############################################################################

InstallImmediateMethod(IsTrivial, IsMonoid and HasGeneratorsOfMonoid, 0,
function(S)
  local gens;
  gens := GeneratorsOfMonoid(S);
  if CanEasilyCompareElements(gens) and Length(gens) = 1
      and gens[1] = One(gens) then
    return true;
  fi;
  TryNextMethod();
end);

InstallImmediateMethod(IsTrivial, IsMonoid and HasGeneratorsOfSemigroup, 0,
function(S)
  local gens;
  gens := GeneratorsOfSemigroup(S);
  if CanEasilyCompareElements(gens) and Length(gens) = 1
      and gens[1] = One(gens) then
    return true;
  fi;
  TryNextMethod();
end);

InstallMethod(MagmaByGenerators,
"for a finite associative element collection",
[IsAssociativeElementCollection and IsFinite], SemigroupByGenerators);

InstallMethod(SemigroupByGenerators,
"for a finite multiplicative element collection",
[IsMultiplicativeElementCollection and IsFinite],
function(coll)
  return SemigroupByGenerators(coll, SEMIGROUPS.DefaultOptionsRec);
end);

InstallMethod(SemigroupByGenerators,
"for a finite multiplicative element collection and record",
[IsMultiplicativeElementCollection and IsFinite, IsRecord],
function(gens, opts)
  local filts, S;

  opts := SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.DefaultOptionsRec, opts);

  if CanEasilyCompareElements(gens) then
    # Check if the One of the generators is a generator
    if IsMultiplicativeElementWithOneCollection(gens)
        and Position(gens, One(gens)) <> fail then
      return MonoidByGenerators(gens, opts);
    fi;

    # Try to find a smaller generating set
    if opts.small and Length(gens) > 1 then
      opts := ShallowCopy(opts);
      opts.small := false;
      opts.regular := false;
      return ClosureSemigroup(Semigroup(gens[1], opts), gens, opts);
    fi;
  fi;

  filts := IsSemigroup and IsAttributeStoringRep;

  if opts.regular then  # This overrides everything!
    filts := filts and IsRegularActingSemigroupRep;
  elif opts.acting and IsGeneratorsOfActingSemigroup(gens) then
    filts := filts and IsActingSemigroup;
  fi;

  S := Objectify(NewType(FamilyObj(gens), filts), rec(opts := opts));
  SetGeneratorsOfMagma(S, AsList(gens));

  return S;
end);

InstallMethod(MonoidByGenerators,
"for a finite multiplicative element collection",
[IsMultiplicativeElementCollection and IsFinite],
function(gens)
  return MonoidByGenerators(gens, SEMIGROUPS.DefaultOptionsRec);
end);

InstallMethod(MonoidByGenerators,
"for a finite multiplicative element collection and record",
[IsMultiplicativeElementCollection and IsFinite, IsRecord],
function(gens, opts)
  local mgens, pos, filts, S;

  opts := SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.DefaultOptionsRec, opts);
  mgens := ShallowCopy(gens);

  if CanEasilyCompareElements(gens) then
    # Try to find a smaller generating set
    if opts.small and Length(gens) > 1 then
      opts         := ShallowCopy(opts);
      opts.small   := false;
      opts.regular := false;
      return ClosureMonoid(Monoid(One(gens), opts), gens, opts);
    elif IsMultiplicativeElementWithOneCollection(gens)
        and Length(gens) > 1 then
      pos := Position(gens, One(gens));
      if pos <> fail and
          (not IsPartialPermCollection(gens) or One(gens) =
           One(gens{Concatenation([1 .. pos - 1],
                                  [pos + 1 .. Length(gens)])})) then
        Remove(mgens, pos);
      fi;
    fi;
  fi;

  filts := IsMonoid and IsAttributeStoringRep;

  if opts.regular then  # This overrides everything!
    filts := filts and IsRegularActingSemigroupRep;
  elif opts.acting and IsGeneratorsOfActingSemigroup(gens) then
    filts := filts and IsActingSemigroup;
  fi;

  S := Objectify(NewType(FamilyObj(gens), filts), rec(opts := opts));

  if not CanEasilyCompareElements(gens) or not One(gens) in gens then
    SetGeneratorsOfMagma(S, Concatenation([One(gens)], gens));
  else
    SetGeneratorsOfMagma(S, AsList(gens));
  fi;
  SetGeneratorsOfMagmaWithOne(S, AsList(mgens));

  return S;
end);

InstallMethod(InverseSemigroupByGenerators,
"for a finite collection",
[IsCollection and IsFinite],
function(gens)
  return InverseSemigroupByGenerators(gens, SEMIGROUPS.DefaultOptionsRec);
end);

InstallMethod(InverseSemigroupByGenerators,
"for a finite multiplicative element collection and record",
[IsMultiplicativeElementCollection and IsFinite, IsRecord],
function(gens, opts)
  local filts, S;

  if not IsGeneratorsOfInverseSemigroup(gens) then
    ErrorNoReturn("the 1st argument (a finite mult. elt. coll.) must satisfy ",
                  "IsGeneratorsOfInverseSemigroup");
  fi;

  opts := SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.DefaultOptionsRec, opts);

  if CanEasilyCompareElements(gens) then
    # Check if the One of the generators is a generator
    if IsMultiplicativeElementWithOneCollection(gens)
        and Position(gens, One(gens)) <> fail then
      return InverseMonoidByGenerators(gens, opts);
    elif opts.small and Length(gens) > 1 then
      # Try to find a smaller generating set
      opts := ShallowCopy(opts);
      opts.small := false;
      return ClosureInverseSemigroup(InverseSemigroup(gens[1], opts),
                                     gens,
                                     opts);
    fi;
  fi;

  filts := IsMagma and IsInverseSemigroup and IsAttributeStoringRep;

  if opts.acting and IsGeneratorsOfActingSemigroup(gens) then
    filts := filts and IsInverseActingSemigroupRep;
  fi;

  S := Objectify(NewType(FamilyObj(gens), filts), rec(opts := opts));
  SetGeneratorsOfInverseSemigroup(S, AsList(gens));

  return S;
end);

InstallMethod(InverseMonoidByGenerators,
"for a finite collection",
[IsCollection and IsFinite],
function(gens)
  return InverseMonoidByGenerators(gens, SEMIGROUPS.DefaultOptionsRec);
end);

InstallMethod(InverseMonoidByGenerators,
"for a finite multiplicative element collection and record",
[IsMultiplicativeElementCollection and IsMultiplicativeElementWithOneCollection
 and IsFinite, IsRecord],
function(gens, opts)
  local pos, filts, S;

  if not IsGeneratorsOfInverseSemigroup(gens) then
    ErrorNoReturn("the 1st argument (a finite mult. elt. coll.) must satisfy ",
                  "IsGeneratorsOfInverseSemigroup");
  fi;

  opts := SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.DefaultOptionsRec, opts);

  if CanEasilyCompareElements(gens) then
    if (not IsPartialPermCollection(gens) or not opts.small)
        and IsMultiplicativeElementWithOneCollection(gens)
        and Length(gens) > 1 then
      pos := Position(gens, One(gens));
      if pos <> fail and
          (not IsPartialPermCollection(gens) or One(gens) =
           One(gens{Concatenation([1 .. pos - 1],
                                  [pos + 1 .. Length(gens)])})) then
        gens := ShallowCopy(gens);
        Remove(gens, pos);
      fi;
    fi;
    if opts.small and Length(gens) > 1 then
      # Try to find a smaller generating set
      opts := ShallowCopy(opts);
      opts.small := false;
      return ClosureInverseMonoid(InverseMonoid(One(gens), opts),
                                  gens,
                                  opts);
    fi;
  fi;

  filts := IsMagmaWithOne and IsInverseMonoid and IsAttributeStoringRep;

  if opts.acting and IsGeneratorsOfActingSemigroup(gens) then
    filts := filts and IsInverseActingSemigroupRep;
  fi;

  S := Objectify(NewType(FamilyObj(gens), filts), rec(opts := opts));
  SetOne(S, One(gens));

  SetGeneratorsOfInverseMonoid(S, AsList(gens));
  if not CanEasilyCompareElements(gens) or not One(gens) in gens then
    SetGeneratorsOfInverseSemigroup(S, Concatenation(gens, [One(gens)]));
  else
    SetGeneratorsOfInverseSemigroup(S, AsList(gens));
  fi;
  return S;
end);

#############################################################################
## 4. RegularSemigroup
#############################################################################

InstallGlobalFunction(RegularSemigroup,
function(arg)
  if not IsRecord(arg[Length(arg)]) then
    Add(arg, rec(regular := true));
  else
    arg[Length(arg)].regular := true;
  fi;
  return CallFuncList(Semigroup, arg);
end);

#############################################################################
## 5. ClosureSemigroup/Monoid
#############################################################################

InstallMethod(ClosureSemigroup,
"for a semigroup and finite multiplicative element collection",
[IsSemigroup, IsMultiplicativeElementCollection and IsFinite],
function(S, coll)
  return ClosureSemigroup(S, coll, SEMIGROUPS.OptionsRec(S));
end);

InstallMethod(ClosureMonoid,
"for a monoid and finite mult. element with one collection",
[IsMonoid, IsMultiplicativeElementWithOneCollection and IsFinite],
function(S, coll)
  return ClosureMonoid(S, coll, SEMIGROUPS.OptionsRec(S));
end);

InstallMethod(ClosureSemigroup, "for a semigroup and multiplicative element",
[IsSemigroup, IsMultiplicativeElement],
function(S, x)
  return ClosureSemigroup(S, [x], SEMIGROUPS.OptionsRec(S));
end);

InstallMethod(ClosureMonoid, "for a monoid and mult. element with one",
[IsMonoid, IsMultiplicativeElementWithOne],
function(S, x)
  return ClosureMonoid(S, [x], SEMIGROUPS.OptionsRec(S));
end);

InstallMethod(ClosureSemigroup,
"for a semigroup, multiplicative element, and record",
[IsSemigroup, IsMultiplicativeElement, IsRecord],
function(S, x, opts)
  return ClosureSemigroup(S, [x], opts);
end);

InstallMethod(ClosureMonoid,
"for a monoid, mult. element with one, and record",
[IsMonoid, IsMultiplicativeElementWithOne, IsRecord],
function(S, x, opts)
  return ClosureMonoid(S, [x], opts);
end);

InstallMethod(ClosureSemigroup,
"for a semigroup, finite multiplicative element collection, and record",
[IsSemigroup, IsMultiplicativeElementCollection and IsFinite, IsRecord],
function(S, coll, opts)

  # coll is copied here to avoid doing it repeatedly in
  # ClosureSemigroupOrMonoidNC

  if IsSemigroup(coll) then
    coll := GeneratorsOfSemigroup(coll);
  elif not IsList(coll) then
    coll := AsList(coll);
  fi;

  if not IsMutable(coll) then
    coll := ShallowCopy(coll);
  fi;

  # This error has to come after coll is turned into a list, otherwise it may
  # fail in Concatenation(GeneratorsOfSemigroup(S), coll).

  if ElementsFamily(FamilyObj(S)) <> FamilyObj(Representative(coll))
      or not IsGeneratorsOfSemigroup(Concatenation(GeneratorsOfSemigroup(S),
                                                   coll)) then
    ErrorNoReturn("the 1st argument (a semigroup) and the 2nd argument ",
                  "(a mult. elt. coll.) cannot be used to ",
                  "generate a semigroup");
  fi;

  # opts is copied and processed here to avoid doing it repeatedly in
  # ClosureSemigroupOrMonoidNC

  opts         := ShallowCopy(opts);
  opts.small   := false;
  opts.regular := false;
  opts         := SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.DefaultOptionsRec,
                                               opts);

  return ClosureSemigroupOrMonoidNC(Semigroup, S, coll, opts);
end);

InstallMethod(ClosureMonoid,
"for a monoid, finite multiplicative with one element collection, and record",
[IsMonoid, IsMultiplicativeElementWithOneCollection and IsFinite, IsRecord],
function(S, coll, opts)
  # coll is copied here to avoid doing it repeatedly in
  # ClosureSemigroupOrMonoidNC

  if IsSemigroup(coll) then
    coll := ShallowCopy(GeneratorsOfSemigroup(coll));
  elif not IsList(coll) then
    coll := AsList(coll);
  fi;

  if not IsMutable(coll) then
    coll := ShallowCopy(coll);
  fi;

  # This error has to come after coll is turned into a list, otherwise it may
  # fail in Concatenation(GeneratorsOfSemigroup(S), coll).

  if ElementsFamily(FamilyObj(S)) <> FamilyObj(Representative(coll))
      or not IsGeneratorsOfSemigroup(Concatenation(GeneratorsOfSemigroup(S),
                                                   coll)) then
    ErrorNoReturn("the 1st argument (a monoid) and the 2nd argument ",
                  "(a mult. elt. with one coll.) cannot be ",
                  "used to generate a monoid");
  fi;

  # opts is copied and processed here to avoid doing it repeatedly in
  # ClosureSemigroupOrMonoidNC

  opts         := ShallowCopy(opts);
  opts.small   := false;
  opts.regular := false;
  opts         := SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.DefaultOptionsRec,
                                               opts);

  return ClosureSemigroupOrMonoidNC(Monoid, S, coll, opts);
end);

InstallMethod(ClosureSemigroupOrMonoidNC,
"for a function, semigroup, finite mult. element collection, and record",
[IsFunction,
 IsSemigroup,
 IsMultiplicativeElementCollection and IsFinite and IsList,
 IsRecord],
function(Constructor, S, coll, opts)
  local n;

  # opts must be copied and processed before calling this function
  # coll must be copied before calling this function

  coll := Filtered(coll, x -> not x in S);
  if IsEmpty(coll) then
    return S;
  fi;

  coll := Shuffle(Set(coll));
  if IsGeneratorsOfActingSemigroup(coll) then
    n := ActionDegree(coll);
    Sort(coll, {x, y} -> ActionRank(x, n) > ActionRank(y, n));
  elif Length(coll) < 120 then
    Sort(coll, IsGreensDGreaterThanFunc(Semigroup(coll)));
  fi;

  return Constructor(S, coll, opts);
end);

# Both of these methods are required for ClosureSemigroup(NC) and an empty list
# because ClosureSemigroup might be called with an empty list, it might be that
# all of the elements in the collection passed to ClosureSemigroup already
# belong to the semigroup, in which case we call ClosureSemigroupNC with an
# empty list.

InstallMethod(ClosureSemigroup,
"for a semigroup, empty list or collection, and record",
[IsSemigroup, IsListOrCollection and IsEmpty, IsRecord],
{S, coll, opts} -> S);

InstallMethod(ClosureSemigroupOrMonoidNC,
"for a function, a semigroup, empty list, and record",
[IsFunction, IsSemigroup, IsList and IsEmpty, IsRecord],
{Construction, S, coll, opts} -> S);

#############################################################################
## 5. ClosureInverseSemigroup
#############################################################################

InstallMethod(ClosureInverseSemigroup,
"for an inverse semigroup with inverse op and finite mult. element coll",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementCollection and IsFinite],
function(S, coll)
  return ClosureInverseSemigroup(S, coll, SEMIGROUPS.OptionsRec(S));
end);

InstallMethod(ClosureInverseMonoid,
"for an inverse monoid with inverse op and finite mult. element with one coll",
[IsInverseMonoid and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementWithOneCollection and IsFinite],
function(S, coll)
  return ClosureInverseMonoid(S, coll, SEMIGROUPS.OptionsRec(S));
end);

InstallMethod(ClosureInverseSemigroup,
"for an inverse semigroup with inverse op and a multiplicative element",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElement],
function(S, x)
  return ClosureInverseSemigroup(S, [x], SEMIGROUPS.OptionsRec(S));
end);

InstallMethod(ClosureInverseMonoid,
"for an inverse monoid with inverse op and a mult. element with one",
[IsInverseMonoid and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementWithOne],
function(S, x)
  return ClosureInverseMonoid(S, [x], SEMIGROUPS.OptionsRec(S));
end);

InstallMethod(ClosureInverseSemigroup,
"for inverse semigroup with inverse op, multiplicative element, record",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElement,
 IsRecord],
function(S, x, opts)
  return ClosureInverseSemigroup(S, [x], opts);
end);

InstallMethod(ClosureInverseMonoid,
"for inverse monoid with inverse op, multiplicative element with one, record",
[IsInverseMonoid and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementWithOne,
 IsRecord],
function(S, x, opts)
  return ClosureInverseMonoid(S, [x], opts);
end);

InstallMethod(ClosureInverseSemigroup,
"for an inverse semigroup with inverse op, finite mult elt coll, and record",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementCollection and IsFinite,
 IsRecord],
function(S, coll, opts)

  # coll is copied here to avoid doing it repeatedly in
  # ClosureSemigroupOrMonoidNC

  if not IsGeneratorsOfInverseSemigroup(coll) then
    ErrorNoReturn("the 2nd argument (a finite mult. elt. coll.) must satisfy ",
                  "IsGeneratorsOfInverseSemigroup");
  elif IsSemigroup(coll) then
    coll := ShallowCopy(GeneratorsOfSemigroup(coll));
  elif not IsList(coll) then
    coll := AsList(coll);
  else
    coll := ShallowCopy(coll);
  fi;

  # This error has to come after coll is turned into a list, otherwise it may
  # fail in Concatenation(GeneratorsOfSemigroup(S), coll).

  if ElementsFamily(FamilyObj(S)) <> FamilyObj(Representative(coll))
      or not IsGeneratorsOfSemigroup(Concatenation(GeneratorsOfSemigroup(S),
                                                   coll)) then
    ErrorNoReturn("the 1st argument (a semigroup) and the 2nd argument ",
                  "(a mult. elt. coll.) cannot be used to ",
                  "generate an inverse semigroup");
  fi;

  # opts is copied and processed here to avoid doing it repeatedly in
  # ClosureInverseSemigroupOrMonoidNC

  opts         := ShallowCopy(opts);
  opts.small   := false;
  opts         := SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.DefaultOptionsRec,
                                               opts);

  return ClosureInverseSemigroupOrMonoidNC(InverseSemigroup, S, coll, opts);
end);

InstallMethod(ClosureInverseMonoid,
"for an inverse monoid, finite mult elt with one coll, and record",
[IsInverseMonoid and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementCollection and IsFinite,
 IsRecord],
function(S, coll, opts)

  # coll is copied here to avoid doing it repeatedly in
  # ClosureSemigroupOrMonoidNC

  if not IsGeneratorsOfInverseSemigroup(coll) then
    ErrorNoReturn("the 2nd argument (a finite mult. elt. coll.) must satisfy ",
                  "IsGeneratorsOfInverseSemigroup");
  elif IsSemigroup(coll) then
    coll := ShallowCopy(GeneratorsOfSemigroup(coll));
  elif not IsList(coll) then
    coll := AsList(coll);
  else
    coll := ShallowCopy(coll);
  fi;

  # This error has to come after coll is turned into a list, otherwise it may
  # fail in Concatenation(GeneratorsOfSemigroup(S), coll).

  if ElementsFamily(FamilyObj(S)) <> FamilyObj(Representative(coll))
      or not IsGeneratorsOfSemigroup(Concatenation(GeneratorsOfSemigroup(S),
                                                   coll)) then
    ErrorNoReturn("the 1st argument (a semigroup) and the 2nd argument ",
                  "(a mult. elt. coll.) cannot be used to ",
                  "generate an inverse monoid");
  fi;

  # opts is copied and processed here to avoid doing it repeatedly in
  # ClosureInverseSemigroupOrMonoidNC

  opts         := ShallowCopy(opts);
  opts.small   := false;
  opts         := SEMIGROUPS.ProcessOptionsRec(SEMIGROUPS.DefaultOptionsRec,
                                               opts);

  return ClosureInverseSemigroupOrMonoidNC(InverseMonoid, S, coll, opts);
end);

InstallMethod(ClosureInverseSemigroupOrMonoidNC,
"for a function, an inverse semigroup, finite list of mult. element, and rec",
[IsFunction,
 IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsMultiplicativeElementCollection and IsFinite and IsList,
 IsRecord],
function(Constructor, S, coll, opts)
  local n, x, one, i;
  coll := Filtered(coll, x -> not x in S);
  if IsEmpty(coll) then
    return S;
  fi;

  # opts must be copied and processed before calling this function
  # coll must be copied before calling this function

  # Make coll closed under inverses
  coll := Set(coll);
  n    := Length(coll);
  for i in [1 .. n] do
    x := coll[i] ^ -1;
    if not x in coll then
      AddSet(coll, x);
    fi;
  od;

  if Constructor = InverseMonoid
      and IsMultiplicativeElementWithOneCollection(S)
      and IsMultiplicativeElementWithOneCollection(coll) then
    one := One(Concatenation(coll, GeneratorsOfSemigroup(S)));
    if not one in coll and not one in S then
      AddSet(coll, one);
    fi;
  fi;

  # Shuffle and sort by rank or the D-order
  coll := Shuffle(coll);
  if IsGeneratorsOfActingSemigroup(coll) then
    n := ActionDegree(coll);
    Sort(coll, {x, y} -> ActionRank(x, n) > ActionRank(y, n));
  elif Length(coll) < 120 then
    Sort(coll, IsGreensDGreaterThanFunc(InverseSemigroup(coll)));
  fi;

  return ClosureSemigroupOrMonoidNC(Constructor, S, coll, opts);
end);

# Both of these methods are required for ClosureInverseSemigroup(NC) and an
# empty list because ClosureInverseSemigroup might be called with an empty
# list, it might be that all of the elements in the collection passed to
# ClosureInverseSemigroup already belong to the semigroup, in which case we
# call ClosureInverseSemigroupOrMonoidNC with an empty list.

InstallMethod(ClosureInverseSemigroup,
"for an inverse semigroup, empty list or collection, and record",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsListOrCollection and IsEmpty,
 IsRecord],
function(S, coll, opts)
  return S;
end);

InstallMethod(ClosureInverseMonoid,
"for an inverse monoid, empty list or collection, and record",
[IsInverseMonoid and IsGeneratorsOfInverseSemigroup,
 IsListOrCollection and IsEmpty,
 IsRecord],
function(S, coll, opts)
  return S;
end);

InstallMethod(ClosureInverseSemigroupOrMonoidNC,
"for a function, inverse semigroup, empty list, and record",
[IsFunction,
 IsInverseSemigroup and IsGeneratorsOfInverseSemigroup,
 IsList and IsEmpty,
 IsRecord],
function(Constructor, S, coll, opts)
  return S;
end);

#############################################################################
## 7. Subsemigroups
#############################################################################

InstallMethod(SubsemigroupByProperty,
"for a semigroup, function, and positive integer",
[IsSemigroup, IsFunction, IsPosInt],
function(S, func, limit)
  local iter, x, closure, T;

  iter := Iterator(S);

  repeat
    x := NextIterator(iter);
  until func(x) or IsDoneIterator(iter);

  if not func(x) then
    return fail;  # should really return the empty semigroup
  elif CanUseLibsemigroupsFroidurePin(S) then
    closure := {S, coll, opts} ->
               ClosureSemigroupOrMonoidNC(Semigroup, S, coll, opts);
  else
    closure := ClosureSemigroup;
  fi;
  T := Semigroup(x);

  while Size(T) < limit and not IsDoneIterator(iter) do
    x := NextIterator(iter);
    if func(x) and not x in T then
      T := closure(T, [x], SEMIGROUPS.OptionsRec(T));
    fi;
  od;
  SetParent(T, S);
  return T;
end);

InstallMethod(InverseSubsemigroupByProperty,
"for an inverse semigroup with inverse op, function, positive integer",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup, IsFunction, IsPosInt],
function(S, func, limit)
  local iter, T, x;

  iter := Iterator(S);

  repeat
    x := NextIterator(iter);
  until func(x) or IsDoneIterator(iter);

  if not func(x) then
    return fail;  # should really return the empty semigroup
  fi;

  T := InverseSemigroup(x);

  while Size(T) < limit and not IsDoneIterator(iter) do
    x := NextIterator(iter);
    if func(x) then
      T := ClosureInverseSemigroup(T, x);
    fi;
  od;
  SetParent(T, S);
  return T;
end);

InstallMethod(SubsemigroupByProperty, "for a semigroup and function",
[IsSemigroup, IsFunction],
function(S, func)
  return SubsemigroupByProperty(S, func, Size(S));
end);

InstallMethod(InverseSubsemigroupByProperty,
"for inverse semigroup with inverse op and function",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup, IsFunction],
function(S, func)
  return InverseSubsemigroupByProperty(S, func, Size(S));
end);

#############################################################################
## 8. Random semigroups and elements
#############################################################################

InstallMethod(Random,
"for a semigroup with AsList",
[IsSemigroup and HasAsList],
20,  # to beat other random methods
function(S)
  return AsList(S)[Random(1, Size(S))];
end);

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsSemigroup, IsList],
function(filt, params)
  if Length(params) < 1 then  # nr gens
    params[1] := Random(1, 20);
  elif not IsPosInt(params[1]) then
    return "the 2nd argument (number of generators) must be a pos int";
  fi;
  if Length(params) < 2 then  # degree / dimension
    params[2] := Random(1, 20);
  elif not IsPosInt(params[2]) then
    return "the 3rd argument (degree or dimension) must be a pos int";
  fi;
  if Length(params) > 2 then
    return "there must be at most 3 arguments";
  fi;
  return params;
end);

InstallMethod(SEMIGROUPS_ProcessRandomArgsCons,
[IsMonoid, IsList],
function(filt, params)
  return SEMIGROUPS_ProcessRandomArgsCons(IsSemigroup, params);
end);

SEMIGROUPS.DefaultRandomInverseSemigroup := function(filt, params)
  if Length(params) = 2 then
    return AsSemigroup(filt,
                       RandomInverseSemigroup(IsPartialPermSemigroup,
                                              params[1],
                                              params[2]));
  elif Length(params) = 3 then
    return AsSemigroup(filt,
                       params[3],  # threshold
                       RandomInverseSemigroup(IsPartialPermSemigroup,
                                              params[1],
                                              params[2]));
  elif Length(params) = 4 then
    return AsSemigroup(filt,
                       params[3],  # threshold
                       params[4],  # period
                       RandomInverseSemigroup(IsPartialPermSemigroup,
                                              params[1],
                                              params[2]));
  fi;
  ErrorNoReturn("the 2nd argument must have length 2, 3, or 4");
end;

SEMIGROUPS.DefaultRandomInverseMonoid := function(filt, params)
  if Length(params) = 2 then
    return AsMonoid(filt,
                    RandomInverseMonoid(IsPartialPermMonoid,
                                        params[1],
                                        params[2]));
  elif Length(params) = 3 then
    return AsMonoid(filt,
                    params[3],  # threshold
                    RandomInverseMonoid(IsPartialPermMonoid,
                                        params[1],
                                        params[2]));
  elif Length(params) = 4 then
    return AsMonoid(filt,
                    params[3],  # threshold
                    params[4],  # period
                    RandomInverseMonoid(IsPartialPermMonoid,
                                        params[1],
                                        params[2]));
  fi;
  ErrorNoReturn("the 2nd argument must have length 2, 3, or 4");
end;

InstallGlobalFunction(RandomSemigroup,
function(arg)
  local filt, params;

  # check for optional first arg
  if Length(arg) >= 1 and IsPosInt(arg[1]) then
    CopyListEntries(arg, 1, 1, arg, 2, 1, Length(arg));
    Unbind(arg[1]);
  fi;

  if Length(arg) >= 1 and IsBound(arg[1]) then
    filt := arg[1];
    if not IsFilter(filt) then
      ErrorNoReturn("the 1st argument must be a filter");
    fi;
  else
    filt := Random([IsReesMatrixSemigroup,
                    IsReesZeroMatrixSemigroup,
                    IsFpSemigroup,
                    IsPBRSemigroup,
                    IsBipartitionSemigroup,
                    IsBlockBijectionSemigroup,
                    IsTransformationSemigroup,
                    IsPartialPermSemigroup,
                    IsBooleanMatSemigroup,
                    IsMaxPlusMatrixSemigroup,
                    IsMinPlusMatrixSemigroup,
                    IsTropicalMaxPlusMatrixSemigroup,
                    IsTropicalMinPlusMatrixSemigroup,
                    IsProjectiveMaxPlusMatrixSemigroup,
                    IsNTPMatrixSemigroup,
                    IsIntegerMatrixSemigroup,
                    IsMatrixOverFiniteFieldSemigroup]);
  fi;

  params := SEMIGROUPS_ProcessRandomArgsCons(filt, arg{[2 .. Length(arg)]});
  if IsString(params) then
    ErrorNoReturn(params);
  fi;
  return RandomSemigroupCons(filt, params);
end);

InstallGlobalFunction(RandomMonoid,
function(arg)
  local filt, params;

  # check for optional first arg
  if Length(arg) >= 1 and IsPosInt(arg[1]) then
    CopyListEntries(arg, 1, 1, arg, 2, 1, Length(arg));
    Unbind(arg[1]);
  fi;

  if Length(arg) >= 1 and IsBound(arg[1]) then
    filt := arg[1];
    if not IsFilter(filt) then
      ErrorNoReturn("the 1st argument must be a filter");
    fi;
  else
    filt := Random([IsFpMonoid,
                    IsPBRMonoid,
                    IsBipartitionMonoid,
                    IsTransformationMonoid,
                    IsPartialPermMonoid,
                    IsBooleanMatMonoid,
                    IsMaxPlusMatrixMonoid,
                    IsMinPlusMatrixMonoid,
                    IsTropicalMaxPlusMatrixMonoid,
                    IsTropicalMinPlusMatrixMonoid,
                    IsProjectiveMaxPlusMatrixMonoid,
                    IsNTPMatrixMonoid,
                    IsBlockBijectionMonoid,
                    IsIntegerMatrixMonoid,
                    IsMatrixOverFiniteFieldMonoid]);
  fi;

  params := SEMIGROUPS_ProcessRandomArgsCons(filt, arg{[2 .. Length(arg)]});
  if IsString(params) then
    ErrorNoReturn(params);
  fi;
  return RandomMonoidCons(filt, params);
end);

InstallGlobalFunction(RandomInverseSemigroup,
function(arg)
  local filt, params;

  # check for optional first arg
  if Length(arg) >= 1 and IsPosInt(arg[1]) then
    CopyListEntries(arg, 1, 1, arg, 2, 1, Length(arg));
    Unbind(arg[1]);
  fi;

  if Length(arg) >= 1 and IsBound(arg[1]) then
    filt := arg[1];
    if not IsFilter(filt) then
      ErrorNoReturn("the 1st argument must be a filter");
    fi;
  else
    filt := Random([IsFpSemigroup,
                    IsPBRSemigroup,
                    IsBipartitionSemigroup,
                    IsTransformationSemigroup,
                    IsPartialPermSemigroup,
                    IsBooleanMatSemigroup,
                    IsMaxPlusMatrixSemigroup,
                    IsMinPlusMatrixSemigroup,
                    IsTropicalMaxPlusMatrixSemigroup,
                    IsTropicalMinPlusMatrixSemigroup,
                    IsProjectiveMaxPlusMatrixSemigroup,
                    IsNTPMatrixSemigroup,
                    IsBlockBijectionSemigroup,
                    IsIntegerMatrixSemigroup,
                    IsMatrixOverFiniteFieldSemigroup]);
  fi;

  params := SEMIGROUPS_ProcessRandomArgsCons(filt, arg{[2 .. Length(arg)]});
  if IsString(params) then
    ErrorNoReturn(params);
  fi;
  return RandomInverseSemigroupCons(filt, params);
end);

InstallGlobalFunction(RandomInverseMonoid,
function(arg)
  local filt, params;

  # check for optional first arg
  if Length(arg) >= 1 and IsPosInt(arg[1]) then
    CopyListEntries(arg, 1, 1, arg, 2, 1, Length(arg));
    Unbind(arg[1]);
  fi;

  if Length(arg) >= 1 and IsBound(arg[1]) then
    filt := arg[1];
    if not IsFilter(filt) then
      ErrorNoReturn("the 1st argument must be a filter");
    fi;
  else
    filt := Random([IsFpMonoid,
                    IsPBRMonoid,
                    IsBipartitionMonoid,
                    IsTransformationMonoid,
                    IsPartialPermMonoid,
                    IsBooleanMatMonoid,
                    IsMaxPlusMatrixMonoid,
                    IsMinPlusMatrixMonoid,
                    IsTropicalMaxPlusMatrixMonoid,
                    IsTropicalMinPlusMatrixMonoid,
                    IsProjectiveMaxPlusMatrixMonoid,
                    IsNTPMatrixMonoid,
                    IsBlockBijectionMonoid,
                    IsIntegerMatrixMonoid,
                    IsMatrixOverFiniteFieldMonoid]);
  fi;

  params := SEMIGROUPS_ProcessRandomArgsCons(filt, arg{[2 .. Length(arg)]});
  if IsString(params) then
    ErrorNoReturn(params);
  fi;
  return RandomInverseMonoidCons(filt, params);
end);

#############################################################################
## 9. Changing representation: AsSemigroup, AsMonoid
#############################################################################

# IsomorphismSemigroup can be used to find an isomorphism from any semigroup to
# a semigroup of any other type (provided a method is installed!). This is done
# to avoid having to have an operation/attribute called IsomorphismXSemigroup
# for every single type of semigroup (X = Bipartition, MaxPlusMatrix, etc).
# This is simpler but has the disadvantage that the isomorphisms are not stored
# as attributes, and slightly more typing is required.
#
# The following IsomorphismXSemigroup functions remain:
#
# - IsomorphismTransformationSemigroup/Monoid
# - IsomorphismPartialPermSemigroup/Monoid
# - IsomorphismFpSemigroup/Monoid
# - IsomorphismRees(Zero)MatrixSemigroup
#
# since they are defined in the GAP library, and, in some sense, are
# fundamental and so it is desirable that they are stored as attributes. The
# method for IsomorphismSemigroup(IsTransformationSemigroup, S) delegates to
# IsomorphismTransformationSemigroup(S), and similarly for the other types
# listed above.
#
# If introducing a new type IsNewTypeOfSemigroup of semigroup, then the minimum
# requirement is to install a method for:
#
#     IsomorphismSemigroup(IsNewTypeOfSemigroup, IsTransformationSemigroup)
#
# and
#
#     InstallMethod(IsomorphismSemigroup,
#     "for IsNewTypeOfSemigroup and a semigroup",
#     [IsNewTypeOfSemigroup, IsSemigroup],
#     SEMIGROUPS.DefaultIsomorphismSemigroup);
#
# Since every other isomorphism can then be computed by composing with an
# isomorphism to a transformation semigroup. Of course, if a better method is
# known, then this can be installed instead. The default (right regular)
# isomorphism from a semigroup in IsNewTypeOfSemigroup to a transformation
# semigroup will be used, if no better method is installed.
#
# It is necessary that all of the methods for IsomorphismSemigroup in a given
# file have the same filter IsXSemigroup for the first argument.  (i.e.
# methods for IsomorphismSemgroup(IsXSemigroup, ...) must go in the
# corresponding file).  Also the methods for IsomorphismSemigroup must appear
# from lowest to highest rank due to the way that constructors are implemented.
# If they are not in lowest to highest rank order, then the wrong constructor
# method is selected (i.e.  the last applicable one is selected).
#
# IsomorphismMonoid is only really necessary to convert semigroups with
# MultiplicativeNeutralElement, which are not in IsMonoid, to monoids. For
# example,
#
#     gap> S := Monoid(Transformation([1, 4, 6, 2, 5, 3, 7, 8, 9, 9]),
#     >                Transformation([6, 3, 2, 7, 5, 1, 8, 8, 9, 9]));;
#     gap> AsSemigroup(IsBooleanMatSemigroup, S);
#     <monoid of 10x10 boolean matrices with 2 generators>
#     gap> AsMonoid(IsBooleanMatMonoid, S);
#     <monoid of 10x10 boolean matrices with 2 generators>
#     gap> S := Semigroup(Transformation([1, 4, 6, 2, 5, 3, 7, 8, 9, 9]),
#     >                   Transformation([6, 3, 2, 7, 5, 1, 8, 8, 9, 9]));;
#     gap> AsSemigroup(IsBooleanMatSemigroup, S);
#     <semigroup of 10x10 boolean matrices with 2 generators>
#     gap> AsMonoid(IsBooleanMatMonoid, S);
#     <monoid of 8x8 boolean matrices with 2 generators>
#
# The reason that AsSemigroup(IsBooleanMatSemigroup, S) returns a monoid, is
# that in IsomorphismSemigroup the GeneratorsOfSemigroup(S) are used to
# construct generators <gens> for the isomorphic boolean matrix semigroup. But
# GeneratorsOfSemigroup(S) contains the One(S) (since it is a monoid) and so
# when we call Semigroup(gens), Semigroup detects that one of the generators is
# the One of the others, and so returns a monoid.
#
# Note also that in the example of semigroups of pbrs, there is a good
# (semigroup) embedding of the partition monoid, but not a good monoid
# embedding. So, if you do AsSemigroup(IsPBRSemigroup, S) when S is a
# bipartition monoid, it returns a semigroup of pbrs with degree equal to the
# degree of S, whereas if you do AsMonoid(IsPBRMonoid, S), you get a monoid
# where the degree is equal to the size of S plus 1 (since this is computed by
# computing an isomorphic transformation monoid, and then this is embedded, as
# a monoid, into a monoid of pbrs).

InstallMethod(AsSemigroup, "for a filter and a semigroup",
[IsOperation, IsSemigroup],
function(filt, S)

  if Tester(filt)(S) and filt(S) then
    return S;
  elif filt = IsTransformationSemigroup then
    return Range(IsomorphismTransformationSemigroup(S));
  elif filt = IsPartialPermSemigroup then
    return Range(IsomorphismPartialPermSemigroup(S));
  elif filt = IsReesMatrixSemigroup then
    return Range(IsomorphismReesMatrixSemigroup(S));
  elif filt = IsReesZeroMatrixSemigroup then
    return Range(IsomorphismReesZeroMatrixSemigroup(S));
  elif filt = IsFpSemigroup then
    return Range(IsomorphismFpSemigroup(S));
  fi;

  return Range(IsomorphismSemigroup(filt, S));
end);

InstallMethod(AsSemigroup, "for a filter, pos int, a semigroup",
[IsOperation, IsPosInt, IsSemigroup],
function(filt, threshold, S)
  return Range(IsomorphismSemigroup(filt, threshold, S));
end);

InstallMethod(AsSemigroup,
"for a filter, pos int, pos int, a semigroup",
[IsOperation, IsPosInt, IsPosInt, IsSemigroup],
function(filt, threshold, period, S)
  return Range(IsomorphismSemigroup(filt, threshold, period, S));
end);

InstallMethod(AsSemigroup, "for a filter, ring, and semigroup",
[IsOperation, IsRing, IsSemigroup],
function(filt, R, S)
  return Range(IsomorphismSemigroup(filt, R, S));
end);

InstallMethod(AsMonoid, "for a filter and a semigroup",
[IsOperation, IsSemigroup],
function(filt, S)

  if IsMonoid(S) and Tester(filt)(S) and filt(S) then
    return S;
  elif filt = IsTransformationMonoid then
    return Range(IsomorphismTransformationMonoid(S));
  elif filt = IsPartialPermMonoid then
    return Range(IsomorphismPartialPermMonoid(S));
  elif filt = IsFpMonoid then
    return Range(IsomorphismFpMonoid(S));
  fi;

  return Range(IsomorphismMonoid(filt, S));
end);

InstallMethod(AsMonoid, "for a filter, pos int, and a semigroup",
[IsOperation, IsPosInt, IsSemigroup],
function(filt, threshold, S)
  return Range(IsomorphismMonoid(filt, threshold, S));
end);

InstallMethod(AsMonoid,
"for a filter, pos int, pos int, and a semigroup",
[IsOperation, IsPosInt, IsPosInt, IsSemigroup],
function(filt, threshold, period, S)
  return Range(IsomorphismMonoid(filt, threshold, period, S));
end);

InstallMethod(AsMonoid, "for a filter, ring, and semigroup",
[IsOperation, IsRing, IsSemigroup],
function(filt, R, S)
  return Range(IsomorphismMonoid(filt, R, S));
end);

#############################################################################
## 10. Operators
#############################################################################

InstallMethod(\<, "for semigroups in the same family", IsIdenticalObj,
[IsSemigroup, IsSemigroup],
function(S, T)
  local SS, TT, s, t;

  if not IsFinite(S) or not IsFinite(T) then
    TryNextMethod();
  fi;

  SS := IteratorSorted(S);
  TT := IteratorSorted(T);

  while not (IsDoneIterator(SS) or IsDoneIterator(TT)) do
    s := NextIterator(SS);
    t := NextIterator(TT);
    if s <> t then
      return s < t;
    fi;
  od;

  if IsDoneIterator(SS) and IsDoneIterator(TT) then
    return false;  # S = T
  fi;
  return IsDoneIterator(SS);
end);

################################################################################
InstallMethod(Intersection2, "for two semigroups in the same family",
IsIdenticalObj,
[IsSemigroup, IsSemigroup],
function(S, T)
  if IsSubsemigroup(S, T) then
    return T;
  elif IsSubsemigroup(T, S) then
    return S;
  fi;
  TryNextMethod();
end);
