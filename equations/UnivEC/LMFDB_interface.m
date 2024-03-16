intrinsic getrecs(filename::MonStgElt:Delimiter:=":") -> SeqEnum
{ Reads a delimited file, returns list of lists of strings (one list per line). }
    return [Split(r,Delimiter:IncludeEmpty):r in Split(Read(filename))];
end intrinsic;

intrinsic GetModularCurveGenerators(label::., generators::.) -> .
{ Obtain generators of a group given its label from a text file}
  for elt in getrecs(generators:Delimiter:="|") do
    if elt[1] eq label then
      N := StringToInteger(elt[2]);
      gen_str := elt[3];
      gen_list := eval gen_str;
      Mat := MatrixRing(Integers(N),2);
      return [Mat!elt : elt in gen_list];
    end if;
  end for;
  return false;
end intrinsic;
