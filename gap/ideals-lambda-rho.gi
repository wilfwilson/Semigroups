############################################################################
##
#W  ideals-lambda-rho.gi
#Y  Copyright (C) 2013-14                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

#InstallMethod(Enumerate, "for an ideal lambda orb", 
#[IsIdealLambdaOrb], 
#function(o, limit, lookfunc)
#end);

#

InstallMethod(Length, "for a ideal orb", 
[IsIdealOrb],
function(o)
  return Sum(o!.lens);
end);

#

InstallMethod(IsBound\[\], "for an ideal orb and positive integer",
[IsIdealOrb, IsPosInt], 
function(o, i)
  local nr;

  nr:=1;
  while IsBound(o!.orbits[nr]) and i>Length(o!.orbits[nr]) do 
    i:=i-Length(o!.orbits[nr]);
    nr:=nr+1;
  od;
  return IsBound(o!.orbits[nr]) and IsBound(o!.orbits[nr][i]);
end);

#

InstallMethod(ELM_LIST, "for an ideal orb and positive integer",
[IsIdealOrb, IsPosInt], 
function(o, i)
  local nr;

  nr:=1;
  while i>Length(o!.orbits[nr]) do 
    i:=i-Length(o!.orbits[nr]);
    nr:=nr+1;
  od;
  return o!.orbits[nr][i];
end);

#

InstallMethod(\in, "for an object and ideal orb",
[IsObject, IsIdealOrb],
function(obj, o)
  return HTValue(o!.ht, obj)<>fail;
end);

#

InstallMethod(Position, "for an ideal orb, object, zero cyc",
[IsIdealOrb, IsObject, IsZeroCyc],
function(o, obj, n)
  return HTValue(o!.ht, obj);
end);

#

InstallMethod(OrbitGraph, "for an ideal orb",
[IsIdealOrb],
function(o)
  return o!.orbitgraph;
end);

#

InstallMethod(ViewObj, "for a ideal orb", 
[IsIdealOrb],
function(o)
  Print("<");
  if IsClosed(o) then 
    Print("closed ");
  else
    Print("open ");
  fi;
  Print("ideal ");
  if IsIdealLambdaOrb(o) then 
    Print("lambda ");
  else
    Print("rho ");
  fi;
  
  Print("orbit with ", Length(o), " points>");
  return;
end);

#

InstallMethod(IdealLambdaOrb, "for an acting semigroup ideal", 
[IsActingSemigroup and IsSemigroupIdeal],
function(I)
  local record, htopts, fam;
  
  record:=rec();
  record.orbits:=[];      record.lens:=[];    
  record.parent:=I;       record.scc:=[];       
  record.scc_reps:=[];    record.scc_lookup:=[];
  record.schreiergen:=[]; record.schreierpos:=[];
  record.orbitgraph:=[];  record.gens:=GeneratorsOfSemigroup(Parent(I));
  
  htopts:=ShallowCopy(LambdaOrbOpts(I)); 
  htopts.treehashsize:=I!.opts.hashlen.M;
  record.ht:=HTCreate(LambdaFunc(I)(Representative(I)), htopts);
  
  fam:=CollectionsFamily(FamilyObj(LambdaFunc(I)(Representative(I))));
  return Objectify(NewType(fam, IsIdealLambdaOrb), record);
end);

# assumes that <pt> is in <o> already...

InstallGlobalFunction(UpdateIdealLambdaOrb, 
function(o, pt)
  local I, record, len, new, ht, i;

  I:=o!.parent; 
  record:=ShallowCopy(LambdaOrbOpts(I));
  
  record.schreier:=true;        record.orbitgraph:=true;
  record.storenumbers:=true;    record.log:=true;
  record.parent:=I;             record.treehashsize:=I!.opts.hashlen.M;
 
  len:=Length(o);

  if len<>0 then 
    record.gradingfunc:=function(new, x)
      return x in o;
    end;
    record.onlygrades:=function(x, data);
      return not x;
    end;
    record.onlygradesdata:=fail;
  fi;

  new:=Orb(GeneratorsOfSemigroup(Parent(I)), pt, LambdaAct(I), record);
  Enumerate(new);
  
  ht:=o!.ht;
  for i in [1..Length(new)] do 
    HTAdd(ht, new[i], i+len);
  od;
  
  o!.scc_reps[Length(o!.scc)+1]:=pt;
  
  # JDM probably don't store these things in <o> since they are already in <new>
  # or remove them from the individual orbits...
  Append(o!.scc_lookup, OrbSCCLookup(new)+Length(o!.scc));
  Append(o!.scc, OrbSCC(new)+len);  
  Append(o!.schreiergen, new!.schreiergen);
  Add(o!.schreierpos, fail);
  for i in [2..Length(new)] do 
    Add(o!.schreierpos, new!.schreierpos[i]+len);
  od;
  Append(o!.orbitgraph, new!.orbitgraph+len);

  o!.orbits[Length(o!.orbits)+1]:=new;
  o!.lens[Length(o!.orbits)]:=Length(new);
  return len+1;
end);

#

InstallMethod(IdealRhoOrb, "for an acting semigroup ideal", 
[IsActingSemigroup and IsSemigroupIdeal],
function(I)
  local record, htopts, fam;
  
  record:=rec();
  record.orbits:=[];      record.lens:=[];    
  record.parent:=I;       record.scc:=[];       
  record.scc_reps:=[];    record.scc_lookup:=[];
  record.schreiergen:=[]; record.schreierpos:=[];
  record.orbitgraph:=[];  record.gens:=GeneratorsOfSemigroup(Parent(I));
  
  htopts:=ShallowCopy(RhoOrbOpts(I)); 
  htopts.treehashsize:=I!.opts.hashlen.M;
  record.ht:=HTCreate(RhoFunc(I)(Representative(I)), htopts);
  
  fam:=CollectionsFamily(FamilyObj(RhoFunc(I)(Representative(I))));
  return Objectify(NewType(fam, IsIdealRhoOrb), record);
end);

# assumes that <pt> is not in <o> already, returns the position of <pt> after it
# is added

InstallGlobalFunction(UpdateIdealRhoOrb, 
function(o, pt)
  local I, record, len, new, ht, i;

  I:=o!.parent; 
  record:=ShallowCopy(RhoOrbOpts(I));
  
  record.schreier:=true;        record.orbitgraph:=true;
  record.storenumbers:=true;    record.log:=true;
  record.parent:=I;             record.treehashsize:=I!.opts.hashlen.M;
  
  len:=Length(o);

  if len<>0 then 
    record.gradingfunc:=function(new, x)
      return x in o;
    end;
    record.onlygrades:=function(x, data);
      return not x;
    end;
    record.onlygradesdata:=fail;
  fi;

  new:=Orb(GeneratorsOfSemigroup(Parent(I)), pt, RhoAct(I), record);
  Enumerate(new);
  
  ht:=o!.ht;
  for i in [1..Length(new)] do 
    HTAdd(ht, new[i], i+len);
  od;
  
  o!.scc_reps[Length(o!.scc)+1]:=pt;
  
  # JDM probably don't store these things in <o> since they are already in <new>
  # or remove them from the individual orbits...
  Append(o!.scc_lookup, OrbSCCLookup(new)+Length(o!.scc));
  Append(o!.scc, OrbSCC(new)+len);  
  Append(o!.schreiergen, new!.schreiergen);
  Add(o!.schreierpos, fail);
  for i in [2..Length(new)] do 
    Add(o!.schreierpos, new!.schreierpos[i]+len);
  od;
  Append(o!.orbitgraph, new!.orbitgraph+len);

  o!.orbits[Length(o!.orbits)+1]:=new;
  o!.lens[Length(o!.orbits)]:=Length(new);
  return len+1;
end);

#

InstallMethod( EvaluateWord, 
"for a semigroup or ideal, a word (Semigroups)",
  [ IsSemigroup, IsList],
  function(S, w)
    return EvaluateWord(S, w, OnRight);
  end);

#

InstallMethod( EvaluateWord, 
"for a semigroup or ideal, a word, and a function (Semigroups)",
  [ IsSemigroup, IsList, IsFunction],
  function(S, w, act)
    local res, gens, i;

    if IsMagmaIdeal(S) then 
      res:=GeneratorsOfSemigroupIdeal(S)[w[1]];
      gens:=GeneratorsOfSemigroup(Parent(S));
    else
      gens:=GeneratorsOfSemigroup(S);
      res:=gens[w[1]];
    fi;
    for i in [2..Length(w)] do
        res := act(res, gens[w[i]]);
    od;
    return res;
  end );

# the first position of the returned word refers to the generators of the ideal
# corresponding to the position in the orbit of the point from which the <o[pos]>
# is obtained. For example, [1,2,3] means I.1*S.2*S.3.

#InstallMethod( TraceSchreierTreeForward, 
#"for an ideal orb and a position (Semigroups)",
#  [ IsIdealOrb, IsPosInt ],
#  function( o, pos )
#    local word;
#    word := [];
#    while o!.schreierpos[pos] <> fail do
#        Add(word,o!.schreiergen[pos]);
#        pos := o!.schreierpos[pos];
#    od;
#    Add(word, o!.genslookup[pos]);
#    return Reversed(word);
#  end );
#
##
#
#
##Usage: o = orbit of images; i = index of scc; j = element of scc[i].
#
## Notes: returns a word in the generators that takes o!.scc[i][1] to o[j] 
## assuming that j in scc[i]
#
#InstallMethod(TraceSchreierTreeOfSCCForward,
#"for an ideal orbit and two positive integers",
#[IsIdealOrb, IsPosInt, IsPosInt],
#function(o, i, j)
#  local tree, scc, word, parent;
#
#  tree:=SchreierTreeOfSCC(o, i);
#  scc:=OrbSCC(o)[i];
#
#  word := [];
#  parent := tree[2][j];
#  while parent  <> fail do
#    Add(word, tree[1][j]);
#    j := parent;
#    parent := tree[2][j];
#  od;
#  
#  Add(word, o!.genslookup[j]);
#  return Reversed(word);
#end);
#
#
#InstallMethod(TraceSchreierTreeOfSCCBack,
#"for an ideal orbit and two positive integers",
#[IsIdealOrb, IsPosInt, IsPosInt],
#function(o, i, j)
#  local tree, mult, scc, word, parent;
#
#  if not IsInvLambdaOrb(o) then
#    tree:=ReverseSchreierTreeOfSCC(o, i);
#    mult:=1;
#  else
#    tree:=SchreierTreeOfSCC(o, i);
#    mult:=-1;
#  fi;
#
#  scc:=OrbSCC(o)[i];
#
#  word := [];
#  parent := tree[2][j];
#  while parent <> fail do
#    Add(word, tree[1][j]);
#    j := parent;
#    parent := tree[2][j];
#  od;
#
#  return word*mult;
#end);
#
#
#
