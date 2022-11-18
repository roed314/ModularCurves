// Usage: ls input_data | parallel --timeout 600 magma -b label:={1} GetModelLMFDB.m
// where input_data is a folder containing one file for each label, consisting of the generators as a comma-separated list of integers

AttachSpec("equations.spec");
SetDebugOnError(true);
if (not assigned label) then
  printf "This script assumes that label, the label of the X_H to compute, is given as a command line paramter.\n";
  printf "Something like magma label:=7.168.3.1 GetModelLMFDB.m\n";
  quit;  
end if;

X, jmap, model_type, cusps := ProcessModel(label);
j := New(JMapData);
j`J := jmap;
System("mkdir -p output_data");
SetColumns(0);
output_fname := Sprintf("output_data/%o.%o", label, model_type);
// Right now all our maps are to P1
output_fname := Sprintf("%o_1.1.0.1.1_%o", output_fname, Degree(Numerator(jmap))); 
LMFDBWriteModel(X, j, cusps, output_fname);
exit;
