
// Call with input := (string) label := (string) output := (string) try_gonal_map:= (true/false)
// (default: true)

// Label should be a.b.c.d.e where a.b.c.d is the modular curve and e is the model type

// Format of input file should be:
// - number of variables
// - equation for the domain, as a big string separated by commas
// enclosed in {} and separated by |

// See below for conventions on variable names

AttachSpec("equations.spec");

// Check input values
if not assigned label then
    print("Error: no label assigned, run with 'label := (string)'");
    exit;
end if;

if #Split(label,".") ne 5 then
    print("Error: label must be (modular curve label).(model type)");
    exit;
end if;

if not assigned output then
    print("Error: no output file assigned, run with 'output := (file name)'");
    exit;
end if;

function ParseBoolean(s)
    if s[1] in ["T", "t", "Y", "y"] then
        return true;
    elif s[1] in ["F", "f", "N", "n"] then
        return false;
    else
        print("Error: invalid boolean (should be true/false/yes/no)");
        exit;
    end if;
end function;

if not assigned try_gonal_map then
    try_gonal_map := true;
else
    try_gonal_map := ParseBoolean(try_gonal_map);
end if;

if not assigned input then
    input := label;
end if;

// Get genus and model type
label := Split(label,".");
genus := StringToInteger(label[3]);
label := Join(label[1..4], ".");



nb_var := StringToInteger(s[1]);
big_equation := s[2];

// Get equations as string
s := Read(input);
s := [ReplaceLetter(ReplaceLetter(x, "{", ""), "}", "") : x in Split(s, "|")]; // List containing:
nb_var, big_equation, jmaps, cusp_coords, cusp_polys, plane_model, model_type := Explode(s);
nb_var := StringToInteger(nb_var);
model_type := StringToInteger(model_type);
// Decide if display
dont_display := #big_equation gt 100000;

// Get equations as polynomials
equations_str := Split(big_equation, ",");
equations_pol := [ReadPoly(s, nb_var): s in equations_str];

// Get j-maps
E4, E6, jmap := Explode(Split(jmaps, "," : IncludeEmpty:=true));
// Get cusps (for now, we only use rational cusps)
Qx<x> := PolynomialRing(Rationals());
cusp_polys := [eval(f) : f in Split(cusp_polys, ",")];
cusp_coords := [
for i in [1..#cusp_polys] do
    f := cusp_polys[i];
    if Degree(f) gt 1 then
        K := NumberField(f);
        AssignNames(~K, Sprintf("a_%o", i));
    end if;
end for;


C := []; // TODO: Read curve model from input data
cusps := []; // TODO: Read cusps from input data
// TODO: Determine whether to try gonal map from input parameters
gon_bounds, plane_models := PlaneModelAndGonalityBounds(equations_pol, C, genus, (model_type eq -1), cusps : try_gonal_map:=true);

// Figure out smoothness
triangular_nbs := [i*(i-1)/2: i in [1..17]];
if model_type eq 0 then
    smooth := true;
elif genus eq 0 then
    smooth := true;
elif not genus in triangular_nbs then
    smooth := false;
elif genus eq 3 then
    if #equations_pol eq 1 and Degree(equations_pol[1]) eq 4 then
	// Smooth plane quartic
	smooth := true;
    else
	smooth := "\\N";
    end if;
elif genus eq 6 then
    // Smooth if models contains a degree 3 relation
    deg_list := [Max(degrees[j]): j in [1..#equations_pol]];
    if 3 in deg_list then
	smooth := true;
    else
	smooth := "\\N";
    end if;
else
    // Do not test for smoothness
    smooth := "\\N";
end if;

// TODO: Write in postgres format rather than for magma input

output_str := "{";
output_str cat:= "'dont_display': " cat Sprint(dont_display) cat ", ";
output_str cat:= "'equation': '" cat big_equation cat "', ";
output_str cat:= "'gonality_bounds': ["
		 cat Sprint(q_low) cat ","
		 cat Sprint(q_high) cat ","
		 cat Sprint(qbar_low) cat ","
		 cat Sprint(qbar_high) cat "], ";
output_str cat:= "'modcurve': '" cat label cat "', ";
output_str cat:= "'model_type': 2, "; //Planar
output_str cat:= "'number_variables': " cat Sprint(nb_var) cat ", ";
output_str cat:= "'smooth': " cat Sprint(smooth) ;
output_str cat:= "}";

SetColumns(0);

Write(output, output_str: Overwrite:=true);
exit;
