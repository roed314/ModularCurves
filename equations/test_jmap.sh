rm -f output_data/30.30.3.1
cd Zywina
magma -b label:=30.30.3.1 GetModelLMFDB.m > ../stdout/30.30.3.1
cd ..
magma -b tests/test_30.30.3.1.m
