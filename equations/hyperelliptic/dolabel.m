load "hyperelliptic/load.m";
load "hyperelliptic/code.m";
g := eval Split(label, ".")[3];
if not assigned prec then
    prec := 100;
else
    prec := StringToInteger(prec);
end if;
if g lt 3 then
    label cat ":genus too small";
    exit;
end if;
function dolabel(label)
    C := HyperellipticModelFromLabel(label : prec:=prec);
    return Join([label, StripWhiteSpace(Sprint(DefiningEquations(C)))], ":");
end function;
if assigned debug then
    SetDebugOnError(true);
    dolabel(label);
else
    try
        dolabel(label);
        exit;
    catch e
        E := Open("/dev/stderr", "w");
        Write(E, Sprint(e) cat "\n");
        Flush(E);
        exit 1;
    end try;
end if;

