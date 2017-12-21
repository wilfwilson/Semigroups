SEMIGROUPS.maximal := rec(cliques := 0,
                          subgroups := 0,
                          constructing := 0,
                          processing := 0,
                          type1 := 0,
                          type2 := 0,
                          type3 := 0,
                          type4 := 0,
                          type5 := 0,
                          type6 := 0,
                          nrtype1 := 0,
                          nrtype2 := 0,
                          nrtype3 := 0,
                          nrtype4 := 0,
                          nrtype5 := 0,
                          nrtype6 := 0);

SEMIGROUPS.elapsed := function(start)
  local stop;
  stop := IO_gettimeofday();
  return (stop.tv_sec - start.tv_sec) * 1000
          + Int((stop.tv_usec - start.tv_usec) / 1000);
end;

single := function(S)
  local start, size, duration_size, max, duration_max;
  SEMIGROUPS.maximal := rec(cliques := 0, subgroups := 0,
                            type1 := 0, type2 := 0, type3 := 0,
                            type4 := 0, type5 := 0, type6 := 0, nrtype1 := 0,
                            nrtype2 := 0, nrtype3 := 0, nrtype4 := 0,
                            nrtype5 := 0, nrtype6 := 0);

  # Compute number maximal subsemigroups (time this, record this)
  #GASMAN("collect");
  start := IO_gettimeofday();
  SEMIGROUPS.maximal.max := NrMaximalSubsemigroups(S);
  SEMIGROUPS.maximal.duration := SEMIGROUPS.elapsed(start);
  return [
    Size(S),
    NrMaximalSubsemigroups(S),
    2,
    0,
    SEMIGROUPS.maximal.duration,
    SEMIGROUPS.maximal.cliques,
    SEMIGROUPS.maximal.subgroups,
    SEMIGROUPS.maximal.type1,
    SEMIGROUPS.maximal.type2,
    SEMIGROUPS.maximal.type3,
    SEMIGROUPS.maximal.type4,
    SEMIGROUPS.maximal.type5,
    SEMIGROUPS.maximal.type6,
    SEMIGROUPS.maximal.nrtype1,
    SEMIGROUPS.maximal.nrtype2,
    SEMIGROUPS.maximal.nrtype3,
    SEMIGROUPS.maximal.nrtype4,
    SEMIGROUPS.maximal.nrtype5,
    SEMIGROUPS.maximal.nrtype6
  ];
end;

#for x in out do
#  for i in x do
#    Print(i, ", ");
#  od;
#  Print("\n");
#od;

profile := function(constructor, n)
  Print("S = ", NameFunction(constructor), "(", n, ")\n");
  return Concatenation([n], single(constructor(n)));
end;

run_profiles := function(constructor, start, stop)
  local collect, n, result, x;
  collect := [];
  for n in [start .. stop] do
    Add(collect, profile(constructor, n));
  od;
  for result in collect do
    for x in result do
      Print(x, ", ");
    od;
    Print("\n");
  od;
end;


#R := BrandtSemigroup(IsReesZeroMatrixSemigroup, CyclicGroup(2), 1000);;
#MaximalSubsemigroups(R, rec(number := true, types := [6]));

random_reg_conn_rzms := function(G, H, i, j)
  local I, J, mat, x, y;
  if not IsGroup(G) then
    ErrorNoReturn("<G> must be a group,");
  elif not IsSubset(G, H) then
    ErrorNoReturn("<H> must be a subset of <G>,");
  elif not IsPosInt(i) or not IsPosInt(j) then
    ErrorNoReturn("<i> and <j> must be positive integers,");
  fi;
  I := [1 .. i];
  J := [1 .. j];
  mat := List(J, x -> I * 0);
  for x in I do
    for y in J do
      if Random([1 .. 2]) = 1 then
        mat[j][i] := Random(H);
      fi;
    od;
  od;
  for x in J do
    mat[x][1] := Random(H);
  od;
  for x in I do
    mat[1][x] := Random(H);
  od;
  return ReesZeroMatrixSemigroup(G, mat);
end;

rzms_union := function(args...)
  local n, group, G, mats, dims_I, dims_J, I, J, mat, offset_I, offset_J,
  matrix, k, j, i;
  n := Length(args);
  if n = 0 then
    ErrorNoReturn("no args given,");
  fi;
  if IsList(args[1]) then
    args := args[1];
    n := Length(args);
  fi;
  if not ForAll(args, IsReesZeroMatrixSemigroup) then
    ErrorNoReturn("all the args must be Rees 0-matrix semigroups,");
  fi;
  group := Set(args, UnderlyingSemigroup);
  if Length(group) <> 1 then
    ErrorNoReturn("all the Rees 0-matrix semigroups must be over the same ",
                  "group,");
  fi;
  G := group[1];
  mats := List(args, Matrix);
  dims_I := List(mats, x -> Length(x[1]));
  dims_J := List(mats, Length);
  I := Sum(dims_I);
  J := Sum(dims_J);
  mat := List([1 .. J], x -> [1 .. I] * 0);
  offset_I := 0;
  offset_J := 0;
  for k in [1 .. n] do
    matrix := mats[k];
    for j in [1 .. Length(matrix)] do
      for i in [1 .. Length(matrix[1])] do
        mat[j + offset_J][i + offset_I] := matrix[j][i];
      od;
    od;
    offset_I := offset_I + dims_I[k];
    offset_J := offset_J + dims_J[k];
  od;
  return ReesZeroMatrixSemigroup(Group(GeneratorsOfGroup(G), One(G)), mat);
end;

random_rzms_comps := function(G, i, j, cc)
  local I, J, subs, H;
  I := Shuffle(Random(Partitions(i, cc)));
  J := Shuffle(Random(Partitions(j, cc)));
  subs := EmptyPlist(cc);
  for i in [1 .. cc] do
    if IsTrivial(G) then
      H := G;
    else
      H := Random(Random(ConjugacyClassesMaximalSubgroups(G)));
    fi;
    subs[i] := random_reg_conn_rzms(G, H, I[i], J[i]);
  od;
  return rzms_union(subs);
end;


# data := List([1 .. 50], x -> EmptyPlist(100));

for dim in [1 .. 20] do
  Print("\ndim = ", dim, "\n\n");
  for x in [1 .. 100] do
    cc := Random([1 .. dim]);
    Print("dim = ", dim, "; x = ", x, ", cc = ", cc, "\n");
    G := Representative(Random(conj));
    R := random_rzms_comps(G, dim, dim, cc);
    new := single(R);
    data[dim][x] := [new[1], new[2], new[5], new[6]];
  od;
od;
