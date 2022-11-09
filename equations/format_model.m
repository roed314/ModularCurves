
// Call with input := (string) label := (string) output := (string) try_gonal_map:= (true/false)

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

if not assigned try_gonal_map then
    try_gonal_map := true;
end if;

if not assigned input then
    input := label;
end if;

// Get labels and model types
label := Split(label,"_");
label1 := label[1];
label2 := label[2];
domain_label : label1[1] cat "." cat label1[2] cat "." cat label1[3] cat "." cat label1[4];
domain_model_type := label1[5];
codomain_label : label2[1] cat "." cat label2[2] cat "." cat label2[3] cat "." cat label2[4];
codomain_model_type := label2[5];

// Get equations as stringe
s := Read(input);
s := Split(s, "{}|"); // List containing: model, (qexp?), map, (N?), nb_var
big_equation := s[1];
nb_var := StringToInteger(s[#s-1]);

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

equations_str := Split(big_equation, ",");
new_equations_str := [];
if nb_var le 26 then    
    // Variables are uppercase letters; use Split to replace
    variables := ["ABCDEFGHIJKLMNOPQRSTUVWXYZ"[i]: i in [(26-nb_var+1)..26]];
    P := PolynomialRing(Rationals(), nb_var);
    AssignNames(~P, variables); // For beautiful debugging    
    for e in equations_str do
	repl := e;
	for i in [1..nb_var] do
	    repl := ReplaceLetter(repl, variables[i], "P." cat Sprint(i));
	end for;
	Append(~new_equations_str, repl);
    end for;
else
    //Variables are X1,...,Xn: replace X by P.
    P<[X]> := PolynomialRing(Rationals(), nb_var);
    for e in equations_str do
	repl := ReplaceLetter(e, "X", "P.");
	Append(new_equations_str, repl);
    end for;
end if;

equations_pol := [eval(pol): pol in new_equations_str];

// Decide if display
dont_display := #equations_str gt 1000;

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
	smooth := "None";
    end if;
elif genus eq 6 then
    // Smooth if models contains a degree 3 relation
    deg_list := [Max(degrees[j]): j in [1..#equations_pol]];
    if 3 in deg_list then
	smooth := true;
    else
	smooth := "None";
    end if;
else
    // Do not test for smoothness
    smooth := "None";
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
