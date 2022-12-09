// Usage: ls input_data | parallel -j80 --timeout 600 "magma -b label:={1} GetModelLMFDB.m >> stdout/{1} 2>&1"
// where input_data is a folder containing one file for each label, consisting of the generators as a comma-separated list of integers

AttachSpec("equations.spec");
SetDebugOnError(true);
if (not assigned label) then
    printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
    printf "Something like magma label:=7.168.3.1 GetModelLMFDB.m\n";
    quit;
end if;

X, jmap, model_type, cusps, M := ProcessModel(label);
j := New(JMapData);
j`J := jmap;
System("mkdir -p output_data");
SetColumns(0);
output_fname := Sprintf("canonical_models/%o.%o", label, model_type);
LMFDBWriteModel(X, j, cusps, output_fname);

// We compute the plane model separately since it can take a long time
if M`genus gt 3 and model_type eq 0 then
    success, plane_model, proj := PlaneModelFromQExpansions(M, X);
    if success then
        output_fname := Sprintf("plane_models/%o", label);
        LMFDBWritePlaneModel(plane_model, proj, output_fname);
    end if;
end if;
exit;
