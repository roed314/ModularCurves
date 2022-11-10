for label in 30.30.3.1 6.6.1.1 6.12.1.1 11.55.1.1 8.48.1.3 9.54.1.1 20.72.1.23 8.96.1.109 1.1.0.1 2.2.0.1 3.6.0.2 10.120.5.3 12.144.3.1 7.168.3.1 24.2304.73.8038
do
    mkdir -p output_data
    mkdir -p stdout
    rm -f output_data/$label*
    rm -f stdout/$label
    echo "Computing model and jmap for curve "$label
    magma -b label:=$label GetModelLMFDB.m > stdout/$label
done
magma -b tests/test_30.30.3.1.m
