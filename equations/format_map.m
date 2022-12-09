
// Call with input := (string) label := (string) output := (string) try_factorization := (true/false) try_extend := (true/false)
// (default: both true)

// Label should be a.b.c.d.e_a'.b'.c'.d'.e'_f
// where a.b.c.d is the domain curve, e is domain model type, similarly for the codomain, and f is the degree

// Format of input file should be:
// - number of variables
// - equation for the domain, as one big string separated by commas
// - equation for coordinates of the map, as one big string separated by commas (no quotients)
// enclosed in {} and separated by |

// See below for conventions on variable names

// Check input values
if not assigned label then
    print("Error: no label assigned, run with 'label := (string)'");
    exit;
end if;

if #Split(label,"._") ne 11 then
    print("Error: incorrect label format, see source code");
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

if not assigned try_factorization then
    try_factorization := true;
else
    try_factorization := ParseBoolean(try_factorization);
end if;

if not assigned try_extend then
    try_extend := true;
else
    try_extend := ParseBoolean(try_extend);
end if;

if not assigned input then
    input := label;
end if;

// Get labels and model types
label := Split(label,"_");
label1 := Split(label[1], ".");
label2 := Split(label[2], ".");
degree := StringToInteger(label[3]);
domain_label := label1[1] cat "." cat label1[2] cat "." cat label1[3] cat "." cat label1[4];
domain_model_type := StringToInteger(label1[5]);
codomain_label := label2[1] cat "." cat label2[2] cat "." cat label2[3] cat "." cat label2[4];
codomain_model_type := StringToInteger(label2[5]);

// Get equations as string
s := Read(input);
s := Split(s, "{}|"); // List containing: nb_var, domain equation, coordinates of map
nb_var := StringToInteger(s[1]);
big_domain_equation := s[2];
big_map_equation := s[3];

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

function PrettyFactorization(F)
    res := "";
    for i := 1 to #F do
	fac := Sprint(F[i][1]);
	if ("+" in fac or "-" in fac) and not (#F eq 1 and F[i][2] eq 1) then
	    res cat:="(" cat fac cat ")";
	else
	    res cat:= fac;
	end if;
	if F[i][2] gt 1 then
	    res cat:= "^" cat Sprint(F[i][2]);
	end if;
	if i lt #F then
	    res cat:="*";
	end if;
    end for;
    return res;
end function;

function StringifyListOfLists(L)
    res := "[";
    for i := 1 to #L do
	res cat:="[";
	res cat:= "'" cat Sprint(L[i][1]) cat "'";
	for j := 2 to #L[i] do
	    res cat:= ",'" cat Sprint(L[i][j]) cat "'";
	end for;
	res cat:= "]";
	if i lt #L then
	    res cat:= ",";
	end if;
    end for;
    res cat:= "]";
    return res;
end function;

// Decide if display
dont_display := #big_map_equation gt 1000;
coordinates_str := Split(big_map_equation, ",");

// Get coordinates as polynomials
if nb_var le 26 then
    var1 := [];
    var2 := [];
    low := Eltseq("xyzwtuvrsabcdefghijklmnopq");
    up := Eltseq("XYZWTUVRSABCDEFGHIJKLMNOPQ");
    for i:=1 to 26 do
	if up[i] in big_domain_equation then
	    Append(~var1, low[i]);
	    Append(~var2, up[i]);
	end if;
    end for;
    if #var1 ne nb_var then
	error "Could not find all variables in domain equation", var2;
    end if;
else
    var1 := ["x" cat Sprint(i): i in [1..nb_var]];
    var2 := ["X" cat Sprint(i): i in [1..nb_var]];
end if;

P := PolynomialRing(Rationals(), nb_var);
AssignNames(~P, var1);
coordinates_pol := [eval(ReplaceVariables(e, var1)): e in coordinates_str];

// Catch maps to P1 given as quotients
if #coordinates_pol eq 1 then
    map := coordinates_pol[1];
    coordinates_pol := [Numerator(map), Denominator(map)];
end if;

// If coordinates are not homogeneous, rescale using last variable
deg := Max([Degree(c): c in coordinates_pol]);
coordinates_pol := [Homogenization(c, P.#var1, deg): c in coordinates_pol];

// Try extending on base locus using Magma generics
if try_extend then
    domain_equations_str := Split(big_domain_equation, ",");
    domain_equations_pol := [eval(ReplaceVariables(e, var2)): e in domain_equations_str];
    ambient := ProjectiveSpace(P);
    C := Curve(ambient, domain_equations_pol);
    T := ProjectiveSpace(Rationals(), #coordinates_pol-1);
    map := map< C -> T | coordinates_pol>;
    map := Extend(map);
    coordinates_all := AllDefiningPolynomials(map);
    nb_opens := #coordinates_all;
else
    coordinates_all := [coordinates_pol];
    nb_opens := 1;
end if;

// Suppress denominators, compute leading coefficients
leading_coefficients_all := []; // List of lists of integers
for i in [1..nb_opens] do
    //Get common denominator
    num := 0;
    den := 1;
    for j in [1..#coordinates_all[i]] do
	den := Lcm(den, Lcm([Denominator(c): c in Coefficients(coordinates_all[i][j])]));
	num := Gcd(num, Gcd([Numerator(c): c in Coefficients(coordinates_all[i][j])]));
    end for;
    coordinates_all[i] := [den/num * c: c in coordinates_all[i]];
    //Get leading coefficients
    lead := [];
    for j in [1..#coordinates_all[i]] do
	num := Gcd([Numerator(c): c in Coefficients(coordinates_all[i][j])]);
	Append(~lead, num);
	coordinates_all[i][j] := 1/num * coordinates_all[i][j];
    end for;
    Append(~leading_coefficients_all, lead);
end for;

// Try factorization, otherwise just convert to strings
coordinates_all_str := [];
for i in [1..nb_opens] do
    coordinates_str := [];
    for j in [1..#coordinates_all[i]] do
	if try_factorization then
	    F := Factorization(coordinates_all[i][j]);
	    Append(~coordinates_str, PrettyFactorization(F));
	    factored := true;
	else
	    Append(~coordinates_str, Sprint(coordinates_all[i][j]));
	    factored := false;
	end if;
    end for;
    Append(~coordinates_all_str, coordinates_str);
end for;
    
output_str := "{";
output_str cat:= "'codomain_label': '" cat codomain_label cat "', ";
output_str cat:= "'codomain_model_type': " cat Sprint(codomain_model_type) cat ", ";
output_str cat:= "'coordinates': " cat StringifyListOfLists(coordinates_all_str) cat ", ";
output_str cat:= "'degree': " cat Sprint(degree) cat ", ";
output_str cat:= "'domain_label': '" cat domain_label cat "', ";
output_str cat:= "'domain_model_type': " cat Sprint(domain_model_type) cat ", ";
output_str cat:= "'dont_display': " cat Sprint(dont_display) cat ", ";
output_str cat:= "'factored': " cat Sprint(factored) cat ", ";
output_str cat:= "'leading_coefficients': '" cat StringifyListOfLists(leading_coefficients_all);
output_str cat:= "}";

SetColumns(0);

Write(output, output_str: Overwrite:=true);
exit;
