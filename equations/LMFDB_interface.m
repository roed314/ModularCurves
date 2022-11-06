// Make sure that you attach CHIMP, e.g. like
// AttachSpec("~/github/CHIMP/CHIMP.spec");

// Expects a line as in modular_curves_data.txt
function GetModularCurveGeneratorsForLine(line) do
    cid, label, level, gen_str := Explode(Split(line, "|"));
    N := StringToInteger(level);
    gen_str := ReplaceCharacter(gen_str, "{", "[");
    gen_str := ReplaceCharacter(gen_str, "}", "]");
    gen_list := eval gen_str;
    Mat := MatrixRing(Integers(N), 2);
    return [Mat!elt : elt in gen_list];
end function;

// Given an LMFDB label for a modular curve, return corresponding generators
function GetModularCurveGenerators(label)
  for elt in getrecs("modular_curves_data.txt":Delimiter:="|") do
    if elt[2] eq label then
      N := StringToInteger(elt[3]);
      gen_str := elt[4];
      gen_str := ReplaceCharacter(gen_str, "{", "[");
      gen_str := ReplaceCharacter(gen_str, "}", "]");
      gen_list := eval gen_str;
      Mat := MatrixRing(Integers(N),2);
      return [Mat!elt : elt in gen_list];
    end if;
  end for;
  return false;
end function;
