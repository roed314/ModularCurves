intrinsic CreateInputDataFile(label::MonStgElt)
{.}
  all_data := Read("modular_curves_data.txt");
  pos := Index(all_data, label);
  eol := Index(all_data[pos..#all_data], "\n");
  substr := all_data[pos+#label..pos+eol-1];
  gens := Split(substr,"|")[2];
  genstr := Join(Split(gens, "{},"), ",");
  genstr := genstr[1..#genstr-2];
  Write("input_data/" * label, genstr : Overwrite);
  return;
end intrinsic;
