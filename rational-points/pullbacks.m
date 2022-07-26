load "new_models.m";

pullback_points := function(X, pairs, N, bound);
    places := [];
    for i in [i : i in [1..#pairs]] do
        pair := pairs[i];
        Y := pair[1];
        rho := pair[2];
        if Genus(Y) eq 0 then 
            continue;
        elif IsHyperelliptic(Y) or Genus(Y) eq 1 then 
            pts := Points(Y : Bound := bound);
        else pts := PointSearch(Y, bound);
        end if;
        for R in pts do 
            place := Pullback(rho, Place(R));
            dec := Decomposition(place);
            if #dec eq 2 or (#dec eq 1 and dec[1][2] eq 2) then  // two rat points or a double rat point so ignore
                continue;
            else places := places cat [dec[1][1]];
            end if;
        end for;
     end for;
        return places;
end function;

// Example 1
        
/*N := 74;
al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
X, _, pairs := eqs_quos(N, al_seq);
bound := 10000;

pullbacks := pullback_points(X,pairs,N, bound); // a few seconds 
    
for PP in pullbacks do
    Discriminant(Integers(ResidueClassField(PP))); // this gives the discriminant of the quadratic field the point lives in
end for;

PP := pullbacks[1];
RepresentativePoint(PP);   // this gives the point (rather than the place)
*/    


// Example 2

/*N := 85;
al_seq := [ [m] : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
X, _, pairs := eqs_quos(N, al_seq);
bound := 10000;

pullbacks := pullback_points(X,pairs,N, bound);    // a few seconds 

for PP in pullbacks do
    Discriminant(Integers(ResidueClassField(PP))); // this gives the discriminant of the quadratic field the point lives in
end for;*/


