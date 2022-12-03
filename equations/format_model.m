
// Call with input := (string) label := (string) output := (string) try_gonal_map:= (true/false)
// (default: true)

// Label should be a.b.c.d.e where a.b.c.d is the modular curve and e is the model type

// Format of input file should be:
// - number of variables
// - equation for the domain, as a big string separated by commas
// enclosed in {} and separated by |

// See below for conventions on variable names

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
model_type := StringToInteger(label[5]);
label := label[1] cat "." cat label[2] cat "." cat label[3] cat "." cat label[4];

// Get equations as string
s := Read(input);
s := Split(s, "{}|"); // List containing: nb_var, equation
nb_var := StringToInteger(s[1]);
big_equation := s[2];

function ReplaceLetter(s, x, subs)
    split := Split(s, x: IncludeEmpty := true);
    res := split[1];
    for j in [2..#split] do
	res := res cat subs cat split[j];
    end for;
    // Even IncludeEmpty does not add "" when s ends with x
    if s[#s] eq x then
	res cat:= subs;
    end if;
    return res;
end function;

function ReplaceVariables(s, variables)
    nb := #variables;
    for i in [1..nb] do
	s := ReplaceLetter(s, variables[i], "P." cat Sprint(i));
    end for;
    return s;
end function;

// Decide if display
dont_display := #big_equation gt 1000;

// Get equations as polynomials
equations_str := Split(big_equation, ",");
new_equations_str := [];
if nb_var le 26 then  // Variables are uppercase letters
    variables := [x: x in Eltseq("ABCDEFGHIJKLMNOPQRSTUVWXYZ") | x in big_equation];
else
    variables := ["X" cat Sprint(i): i in [1..nb_var]];
end if;
P := PolynomialRing(Rationals(), nb_var);
AssignNames(~P, variables);
equations_pol := [eval(ReplaceVariables(s, variables)): s in equations_str];

// Get gonality in low genus
degrees := [[Degree(equations_pol[j], P.i): i in [1..nb_var]]: j in [1..#equations_pol]];
q_high := Min([Min([d: d in degrees[j] | d ne 0]): j in [1..#equations_pol]]);
if genus eq 0 then
    q_low := 1;
    qbar_low := 1;
    qbar_high := 1;
elif genus eq 1 then
    q_low := 2;
    qbar_low := 2;
    qbar_high := 2;
    // Ignore q_high
elif genus eq 2 then
    q_low := 2;
    q_high := 2;
    qbar_low := 2;
    qbar_high := 2;
elif genus le 6 and try_gonal_map then
    ambient := ProjectiveSpace(P);
    curve := Curve(ambient, equations_pol);
    if genus eq 3 then
	qbar_low, map := Genus3GonalMap(curve);
    elif genus eq 4 then
	qbar_low, map := Genus4GonalMap(curve);
    elif genus le 5 then
	qbar_low, map := Genus5GonalMap(curve);
    else
	qbar_low, _, map := Genus6GonalMap(curve);
    end if;
    q_low := qbar_low;
    qbar_high := qbar_low;
    // If gonal map is rational, get q_high as well
    F := BaseField(Domain(map));
    if F eq Rationals() then
	q_high := qbar_high;
    end if;
else
    // Everything is between 2 and q_high
    q_low := 2;
    qbar_low := 2;
    qbar_high := q_high;
end if;

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
