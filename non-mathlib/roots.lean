import field_definition
import field_results
import numbers

/- We can apply an additional contraint onto a field that it has some notion of square roots. 
   It is not necessary to define any properties of square roots other than (sqrt (a) * sqrt (a) = a) . -/ 
class fld_with_sqrt (f : Type) [myfld f] := 
(sqrt : f -> f)
(sqrt_mul_sqrt : ∀ (a : f), myfld.mul (sqrt a) (sqrt a) = a)

lemma sqrt_eq (f : Type) [myfld f] [fld_with_sqrt f] (a b : f) :
  a = b -> (fld_with_sqrt.sqrt a) = (fld_with_sqrt.sqrt b) :=
begin
  intros h, rw h,
end

prefix ` sqroot `:1000002 := fld_with_sqrt.sqrt

@[simp] lemma sqrt_simp (f : Type _) [myfld f] [fld_with_sqrt f] (a : f) : 
      (sqroot a) .* (sqroot a) = a := 
begin rw fld_with_sqrt.sqrt_mul_sqrt a, end 

@[simp] lemma sqrt_squared (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : 
    square f (sqroot  a) = a := 
begin 
  unfold square, rw fld_with_sqrt.sqrt_mul_sqrt a, 
end 

/- We prove that a number can only have two square roots. This will be necessary for proving that 
      the quadratic formula gives all the solutions to a quadratic. 
      The formulation of the lemma is slightly awkward but this way we can do it constructively.-/ 
lemma only_two_square_roots (f : Type) [myfld f] [fld_with_sqrt f] (x y : f) : 
          (x ≠ (sqroot  y)) -> (x ≠ (.- (sqroot  y))) -> (square f x) ≠ y := 
begin 
  unfold square, 
  intros not_sqrt not_minus_sqrt h, 

  have h1 : (x .* x) .+ (.- y) = myfld.zero, 
    rw h, rw myfld.add_negate y, 
  clear h, rename h1 h, 
  have h1 : (x .* x) .+ (((x .* (sqroot  y)) .+ (.- (x .* (sqroot  y)))) .+ (.- y)) = myfld.zero, 
    rw myfld.add_negate (x .* (sqroot  y)), rw simp_zero f _, exact h, 
  clear h, rename h1 h, 
  rw myfld.add_comm (x .* (sqroot  y)) (.- (x .* (sqroot  y))) at h, 
  rw <- myfld.add_assoc (.- (x .* (sqroot  y))) _ _ at h, 
  rw myfld.add_assoc (x .* x) (.- (x .* (sqroot  y))) _ at h, 
  rw mul_negate_alt f x _ at h, 
  rw <- distrib_simp_alt f x x (.- (sqroot  y)) at h, 
  have tmp : (.- y) = .- ((sqroot  y) .* (sqroot  y)), 
    rw fld_with_sqrt.sqrt_mul_sqrt y, 
  rw tmp at h, clear tmp, 
  rw <- mul_negate f (sqroot  y) (sqroot  y) at h, 
  rw <- distrib_simp f _ _ _ at h, 
  rw myfld.mul_comm (x .+ (.- (sqroot  y))) (sqroot  y) at h, 
  rw <- distrib_simp f _ _ _ at h, 

  have tmp : x .+ (sqroot  y) ≠ myfld.zero, 
    intros h1, rw myfld.add_comm at h1, have tmp1 : x = .- (sqroot  y), 
      exact only_one_negation f (sqroot  y) x h1, exact not_minus_sqrt tmp1, 
  have tmp1 : x .+ (.- (sqroot  y)) ≠ myfld.zero, 
    intros h1, rw myfld.add_comm at h1, have tmp1 : x = .- (.- (sqroot  y)), 
      exact only_one_negation f (.- (sqroot  y)) x h1, rw double_negative at tmp1, exact not_sqrt tmp1, 
  exact mul_nonzero f (x .+ (sqroot  y)) (x .+ (.- (sqroot  y))) tmp tmp1 h, 
end 

lemma negative_sqrt (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : 
    ((.- (sqroot  a)) .* (.- (sqroot  a))) = a := 
begin 
  rw mul_negate f _ _, rw <- mul_negate_alt f _ _, rw double_negative f _, 
  exact fld_with_sqrt.sqrt_mul_sqrt a, 
end 

lemma sqrt_ne_zero (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : 
  (a ≠ myfld.zero) -> (sqroot a) ≠ myfld.zero := 
begin 
  intros h1 h2, 
  have h3 : (sqroot a) .* (sqroot a) = myfld.zero, 
    rw h2, rw zero_mul, 
  rw fld_with_sqrt.sqrt_mul_sqrt at h3, cc, 
end 

class fld_with_cube_root (f : Type) [myfld f] := 
(cubrt : f -> f)
(cubrt_cubed : ∀ (a : f), ((cubrt a) .* (cubrt a)) .* (cubrt a) = a)
/- At one point I also had a requirement that (cubrt a) * (cubrt b) = (cubrt (a * b)) . 
This doesn't work. If you have that as a requirement then the following applies: 
Let x = (sqrt (three) - one) /two. (This is one of the alternative cube roots of one)
Then cubrt (x) * cubrt (x) * cubrt (x) = cubrt (x) * cubrt (x) * cubrt (x)
Therefore cubrt (x * x * x) = x 
Therefore cubrt (1) = x 
But you can do a similar argument with 
    cubrt (1) * cubrt (1) * cubrt (1) = cubrt (1) * cubrt (1) * cubrt (1)
  => cubrt (1 * 1 * 1) = 1 
  => cubrt (1) = 1 
  => x = 1 
Therefore all the cube roots of a given number are equal to each other, which is nonsense. 
So we can't do that.-/ 

lemma cubrt_eq (f : Type) [myfld f] [fld_with_cube_root f] (a b : f) :
  a = b -> (fld_with_cube_root.cubrt a) = (fld_with_cube_root.cubrt b) :=
begin
  intros h, rw h,
end

lemma cubrt_cubed (f : Type) [myfld f] [fld_with_cube_root f] (a : f) : (cubed f (fld_with_cube_root.cubrt a)) = a := 
begin 
  unfold cubed, rw myfld.mul_assoc _ _ _, exact fld_with_cube_root.cubrt_cubed _, 
end 

def cubrt_nonzero (f : Type) [myfld f] [fld_with_cube_root f] (a : f) : 
    a ≠ myfld.zero -> (fld_with_cube_root.cubrt a ≠ myfld.zero) := 
begin 
  intros h1 h2, 
  have h3 : cubed f (fld_with_cube_root.cubrt a) = cubed f (myfld.zero), 
    rw h2, 
  rw cubrt_cubed at h3, unfold cubed at h3, rw mul_zero f _ at h3, cc, 
end 

def cube_root_of_unity (f : Type) [myfld f] [fld_not_char_two f] (rt_minus_three : f)
                           (rt_proof : rt_minus_three .* rt_minus_three = (.- (three f))) : f := 
    (((.- myfld.one) .+ rt_minus_three) .* (myfld.reciprocal (two f) (two_ne_zero f)))

lemma cubrt_unity_correct (f : Type) [myfld f] [fld_not_char_two f] (rt_minus_three : f)
                          (rt_proof : rt_minus_three .* rt_minus_three = (.- (three f))) : 
            (cubed f (cube_root_of_unity f rt_minus_three rt_proof)) = myfld.one := 
begin 
  have one_minus_three : myfld.one .+ (.- (three f)) = .- (two f), 
    unfold three, unfold two, rw add_negate f _ _, rw myfld.add_assoc _ _ _, 
    rw myfld.add_negate myfld.one, rw <- zero_add f (.- (myfld.one .+ myfld.one)), 

  /- Start by just doing the root squared. 
     (-1 + sqrt (-3)) ^2 = 1 - sqrt (-3) - sqrt (-3) -3 = -2 (1 + sqrt (-3))
     Doing this as a separate calculation is easier because there's less ambiguity in what I want the prover to do, 
        hence the "have". -/ 
  have square_unfolded : square f ((.- myfld.one) .+ rt_minus_three) = 
                          (.- (two f)) .* (myfld.one .+ rt_minus_three) , 
    unfold square, rw distrib_simp f _ _ _, rw distrib_simp_alt f _ _ _, rw distrib_simp_alt f _ _ _, 
    rw mul_negate f _ _, rw <- mul_negate_alt f _ _, rw mul_negate f _ _, rw double_negative f _, 
    rw one_mul_simp f _, rw one_mul_simp f _, rw rt_proof, rw <- mul_negate_alt f _ _, 
    repeat {rw <- myfld.add_assoc _ _ _}, rw myfld.add_comm myfld.one _, repeat {rw <- myfld.add_assoc _ _ _}, 
    rw myfld.add_comm (.- (three f)) myfld.one, rw one_minus_three, 
    have tmp : (.- rt_minus_three) = rt_minus_three .* (.- myfld.one) , 
      rw <- mul_negate_alt f _ _, rw <- myfld.mul_one rt_minus_three, 
    rw tmp, rw mul_negate_alt f _ _, rw myfld.add_assoc _ _ _, rw <- distrib_simp_alt f rt_minus_three _ _, 
    rw <- add_negate f _ _, 
    clear tmp, have tmp : myfld.one .+ myfld.one = (two f), unfold two, rw tmp, clear tmp, 
    have tmp : (.- (two f)) = (.- (two f)) .* myfld.one,
      exact myfld.mul_one (.- (two f)), rw [tmp] {occs := occurrences.pos [2]}, clear tmp, 
    rw myfld.mul_comm rt_minus_three _, rw <- distrib_simp_alt f (.- (two f)) _ _, 
    rw myfld.add_comm _ _, 

  unfold square at square_unfolded, 
  unfold cube_root_of_unity, rw cube_of_product f _ _, rw cube_of_reciprocal f (two f) _, 
  unfold cubed, rw square_unfolded, clear square_unfolded, 
  /- First cancel the two from the unfolded square with one of the 1/2s.-/ 
  rw myfld.mul_comm ((.- myfld.one) .+ rt_minus_three) _, 
  rw <- myfld.mul_assoc (.- (two f)), 
  rw <- mul_two_reciprocals f (two f) _ _ _, 
  rw myfld.mul_assoc _ (myfld.reciprocal (two f) _) _, rw myfld.mul_comm _ (myfld.reciprocal (two f) _), 
  rw myfld.mul_assoc (myfld.reciprocal (two f) _) (.- (two f)) _, 
  rw myfld.mul_comm (myfld.reciprocal (two f) _) (.- (two f)), 
  rw mul_negate f (two f) _, rw myfld.mul_reciprocal (two f) _, rw mul_negate f _ _, rw one_mul_simp f _, 
  /- Now just a bit of rearranging.-/ 
  rw distrib_simp f _ _ _, rw one_mul_simp f _, rw distrib_simp_alt f _ _ _, 
  rw <- mul_negate_alt f _ _, rw <- myfld.mul_one rt_minus_three, rw rt_proof, 
  repeat {rw <- myfld.add_assoc _ _ _}, rw myfld.add_assoc rt_minus_three (.- rt_minus_three), 
  rw myfld.add_negate rt_minus_three, rw <- zero_add f (.- (three f)), 
  rw <- add_negate f _ _, rw double_negative f _, rw one_plus_three f, 
  rw only_one_reciprocal f ((two f) .* (two f)) _ (mul_nonzero f (two f) (two f) (two_ne_zero f) (two_ne_zero f)), 
  rw myfld.mul_reciprocal ((two f) .* (two f)) (mul_nonzero f (two f) (two f) (two_ne_zero f) (two_ne_zero f)), 
  exact two_ne_zero f, exact (mul_nonzero f (two f) (two f) (two_ne_zero f) (two_ne_zero f)), 
end 

def cubrt_unity_a (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] : f := 
((.- myfld.one) .+ (sqroot  (.- (three f)))) .* (myfld.reciprocal (two f) (two_ne_zero f))

def cubrt_unity_b (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] : f := 
((.- myfld.one) .+ (.- (sqroot  (.- (three f))))) .* (myfld.reciprocal (two f) (two_ne_zero f))


lemma cubrts_unity_sum_zero (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] : 
      myfld.one .+ ((cubrt_unity_a f) .+ (cubrt_unity_b f)) = myfld.zero := 
begin 
  unfold cubrt_unity_a, unfold cubrt_unity_b, 
  rw <- distrib_simp f _ _ (myfld.reciprocal (two f) _), 
  repeat {rw <- myfld.add_assoc}, rw myfld.add_comm _ (.- (sqroot  _)), 
  rw myfld.add_assoc (sqroot  _) (.- (sqroot  _)) _, 
  rw myfld.add_negate (sqroot  _), rw simp_zero f _, 
  rw <- add_negate f myfld.one myfld.one, rw mul_negate f _ _, 
  unfold two, rw myfld.mul_reciprocal (myfld.one .+ myfld.one) _, 
  rw myfld.add_negate myfld.one, 
end 

/-The first of a couple of smaller proofs to move *some* of the tedious algebra away from the proof that has actual interesting 
stuff. Steer clear unless you really like boring algebra. -/ 
/- This first one is a proof that the x^2 term in the cubic for the main proof is zero.-/ 
lemma no_other_cubrts_unity_sub_proof_a (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_with_cube_root f] (a x : f) : 
          (.- (((fld_with_cube_root.cubrt a) .+ (((fld_with_cube_root.cubrt a) .* (cubrt_unity_a f)) .+ ((fld_with_cube_root.cubrt a) .* (cubrt_unity_b f)))) .* (x .* x)))
                        = myfld.zero := 
begin 
  have proof_without_roota : ((myfld.one .+ ((cubrt_unity_a f) .+ (cubrt_unity_b f))) .* (x .* x)) = myfld.zero, 
    unfold cubrt_unity_a, unfold cubrt_unity_b, 
    repeat {rw distrib_simp f _ _ _}, repeat {rw distrib_simp_alt f _ _ _}, repeat {rw distrib_simp f _ _ _}, 
    rw myfld.add_comm ((_ .* (myfld.reciprocal (two f) _)) .* (x .* x))
                      (((.- (sqroot  (.- (three f)))) .* (myfld.reciprocal (two f) _)) .* (x .* x)), 
    repeat {rw myfld.add_assoc _ _ _}, repeat {rw <- myfld.add_assoc _ _ _}, 
    rw myfld.add_assoc (((sqroot  (.- (three f))) .* (myfld.reciprocal (two f) _)) .* (x .* x)) _ _, 
    repeat {rw mul_negate f _ _}, rw myfld.add_negate _, 
    rw <- zero_add f (.- ((myfld.one .* (myfld.reciprocal (two f) _)) .* (x .* x))), 
    repeat {rw one_mul f _}, rw <- add_negate f _ _, rw <- distrib_simp f _ _ (x .* x), 
    rw only_one_reciprocal f (two f) _ (two_ne_zero f), rw add_two_halves f, rw one_mul_simp f, 
    rw myfld.add_negate _, 
  repeat {rw <- myfld.mul_assoc (fld_with_cube_root.cubrt a) _ _}, 
  repeat {rw <- distrib_simp_alt f (fld_with_cube_root.cubrt a) _ _}, 
  rw <- distrib_simp f _ _ (x .* x), 
  rw [myfld.mul_one (x .* x) ] {occs := occurrences.pos [1]}, 
  rw myfld.mul_comm _ (x .* x), rw <- distrib_simp_alt f (x .* x) _ _, 
  rw myfld.mul_comm (x .* x) _, rw proof_without_roota, rw zero_mul f _, rw negate_zero_zero f, 
end 

lemma no_other_cubrts_unity_sub_proof_b (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_with_cube_root f] (a x : f) : 
      (x .* ((((fld_with_cube_root.cubrt a) .* ((fld_with_cube_root.cubrt a) .* (cubrt_unity_a f))) .+ ((fld_with_cube_root.cubrt a) .* ((fld_with_cube_root.cubrt a) .* (cubrt_unity_b f)))) .+ (((fld_with_cube_root.cubrt a) .* (cubrt_unity_a f)) .* ((fld_with_cube_root.cubrt a) .* (cubrt_unity_b f)))))
      = myfld.zero := 
begin 
/- More tedious algebra rearranging. Nothing of interest here.-/ 
  /- This one is proving that the x term in the cubic is zero.-/ 
  repeat {rw myfld.mul_assoc _ (fld_with_cube_root.cubrt a) _}, 
  rw myfld.mul_comm ((fld_with_cube_root.cubrt a) .* (cubrt_unity_a f)) (fld_with_cube_root.cubrt a), 
  rw myfld.mul_assoc (fld_with_cube_root.cubrt a) (fld_with_cube_root.cubrt a) _, 
  rw <- myfld.mul_assoc ((fld_with_cube_root.cubrt a) .* (fld_with_cube_root.cubrt a)) _ _, 
  repeat {rw <- distrib_simp_alt f ((fld_with_cube_root.cubrt a) .* (fld_with_cube_root.cubrt a)) _ _}, 
  unfold cubrt_unity_a, unfold cubrt_unity_b, 
  rw only_one_reciprocal f (two f) _ fld_not_char_two.not_char_two, 
  repeat {rw one_mul_simp f _}, repeat {rw myfld.mul_comm _ (myfld.reciprocal (two f) fld_not_char_two.not_char_two) }, 
  rw <- distrib_simp_alt f (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _ _, 
  rw <- myfld.mul_assoc (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _ _, 
  rw <- distrib_simp_alt f (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _ _, 
  rw myfld.add_comm (.- myfld.one) (.- (sqroot  (.- (three f)))), 
  repeat {rw <- myfld.add_assoc _ _ _}, rw myfld.add_assoc (sqroot  (.- (three f))) _ _, 
  rw myfld.add_negate (sqroot  (.- (three f))), rw simp_zero f _, 
  rw <- add_negate f _ _, rw <- mul_negate_alt f _ _, rw <- mul_negate_alt f _ _, 
  rw <- add_negate f _ _, rw <- add_negate f _ _, rw <- mul_negate_alt f _ _, rw <- mul_negate_alt f _ _, 
  rw distrib_simp f (.- myfld.one) _ _, 
  rw mul_negate f myfld.one _, rw one_mul f _, 
  rw distrib_simp_alt f _ (sqroot  (.- (three f))) _, 
  rw distrib_simp_alt f _ ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (sqroot  (.- (three f)))) _, 
  rw add_negate f ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (sqroot  (.- (three f)))) _, 
  repeat {rw myfld.mul_assoc _ (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _}, 
  repeat {rw myfld.mul_comm _ (myfld.reciprocal (two f) fld_not_char_two.not_char_two) }, 
  repeat {rw <- myfld.mul_assoc (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _ _}, 
  repeat {rw mul_negate_alt f (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _}, 
  repeat {rw <- distrib_simp_alt f (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _ _}, 
  rw fld_with_sqrt.sqrt_mul_sqrt _, rw simp_mul_one f _, 
  repeat {rw myfld.add_assoc _ _ _}, rw myfld.add_comm _ (sqroot  (.- (three f))), 
  repeat {rw myfld.add_assoc _ _ _}, rw myfld.add_negate _, rw simp_zero f _, 
  have three_plus_one : ((.- myfld.one) .+ (.- (three f))) = .- ((two f) .* (two f)), 
    unfold three, unfold two, rw <- add_negate f _ _, rw distrib_simp f _ _ _, rw distrib_simp_alt f _ _ _, 
    rw simp_mul_one f _, repeat {rw myfld.add_assoc _ _ _}, 
  rw three_plus_one, clear three_plus_one, rw <- mul_negate_alt f _ ((two f) .* (two f)), 
  rw myfld.mul_assoc _ (two f) (two f), rw myfld.mul_comm (myfld.reciprocal (two f) _) (two f), 
  rw myfld.mul_reciprocal (two f) _, rw one_mul f _, unfold two, 
  rw myfld.add_negate (myfld.one .+ myfld.one), 
  rw zero_mul f _, rw negate_zero_zero f, rw zero_mul f _, rw zero_mul f _, 
end 

lemma no_other_cubrts (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_with_cube_root f] (a x : f) : 
    (x ≠ (fld_with_cube_root.cubrt a)) -> 
    (x ≠ (fld_with_cube_root.cubrt a) .* (cubrt_unity_a f)) -> 
    (x ≠ (fld_with_cube_root.cubrt a) .* (cubrt_unity_b f)) -> 
    (cubed f x) ≠ a := 
begin 
  /- We demonstrate that multiplying out the cubic formed by (x - 1) (x - root_a) (x - root_b) gives x^3 - 1. 
    Ergo, as we have said that x^3 = 1, one of (x - 1) (x - root_a) (x - root_b) has to be zero, as 
    we cannot multiply nonzero values to get zero.-/ 
  unfold cubrt_unity_a, unfold cubrt_unity_b, 
  intros x_not_one x_not_root_a x_not_root_b, intros h, 
  have multiplied_out_eqn : (factorized_cubic_expression f x (fld_with_cube_root.cubrt a) ((fld_with_cube_root.cubrt a) .* (cubrt_unity_a f)) ((fld_with_cube_root.cubrt a) .* (cubrt_unity_b f)))
             = (cubed f x) .+ (.- a) , 
    rw multiply_out_cubic f _ _ _, 
    /- To make the proof a little cleaner, we simplify the x^2 term, the x term, and the constant separately.-/ 
    rw no_other_cubrts_unity_sub_proof_a f a x, rw simp_zero f _, 
    rw no_other_cubrts_unity_sub_proof_b f a x, rw simp_zero f _, 
    repeat {rw myfld.mul_assoc _ (fld_with_cube_root.cubrt a) _}, 
    rw myfld.mul_comm ((fld_with_cube_root.cubrt a) .* (cubrt_unity_a f)) (fld_with_cube_root.cubrt a), 
    rw myfld.mul_assoc (fld_with_cube_root.cubrt a) (fld_with_cube_root.cubrt a) _, 
    repeat {rw <- myfld.mul_assoc ((fld_with_cube_root.cubrt a) .* (fld_with_cube_root.cubrt a)) _ _}, 
    rw myfld.mul_assoc (fld_with_cube_root.cubrt a) ((fld_with_cube_root.cubrt a) .* (fld_with_cube_root.cubrt a)) _, 
    rw myfld.mul_assoc (fld_with_cube_root.cubrt a) (fld_with_cube_root.cubrt a) (fld_with_cube_root.cubrt a), 
    rw fld_with_cube_root.cubrt_cubed a, 
    unfold cubrt_unity_a, unfold cubrt_unity_b, 
    rw only_one_reciprocal f (two f) _ fld_not_char_two.not_char_two, 
    repeat {rw myfld.mul_comm _ (myfld.reciprocal (two f) fld_not_char_two.not_char_two) }, 
    repeat {rw myfld.mul_assoc _ (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _}, 
    repeat {rw myfld.mul_comm _ (myfld.reciprocal (two f) fld_not_char_two.not_char_two) }, 
    repeat {rw <- myfld.mul_assoc _ _ _}, 
    rw myfld.mul_assoc (myfld.reciprocal (two f) fld_not_char_two.not_char_two) (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _, 
    rw mul_two_reciprocals f (two f) (two f) _ _, 
    repeat {rw distrib_simp f (.- myfld.one) _ _}, repeat {rw distrib_simp_alt f _ (.- myfld.one) _}, 
    repeat {rw mul_negate f _ _}, repeat {rw <- mul_negate_alt f _ _}, rw double_negative f _, 
    rw simp_mul_one f _, rw one_mul_simp f _, rw simp_mul_one f _, rw double_negative f _, 
    rw fld_with_sqrt.sqrt_mul_sqrt (.- (three f)), rw double_negative f _, 
    repeat {rw <- myfld.add_assoc _ _ _}, 
    rw myfld.add_assoc (sqroot  (.- (three f))) (.- (sqroot  (.- (three f)))) _, 
    rw myfld.add_negate (sqroot  (.- (three f))), rw <- zero_add f (three f), 
    have three_plus_one : (myfld.one .+ (three f)) = ((two f) .* (two f)), 
        unfold three, unfold two, rw distrib_simp f _ _ _, rw distrib_simp_alt f _ _ _, 
        rw simp_mul_one f _, repeat {rw myfld.add_assoc _ _ _}, 
    rw three_plus_one, rw myfld.mul_comm (myfld.reciprocal ((two f) .* (two f)) _) ((two f) .* (two f)), 
    rw myfld.mul_reciprocal _ _, rw simp_mul_one f _, 
     /- We have proven that x^3 - 1 = (x - (cubrt (a))) (x - root_1_a* (cubrt (a))) (x - root_1_b* (cubrt (a))) . It is therefore straightforward to prove that no 
      other cube roots of 1 can exist.-/ 
  unfold factorized_cubic_expression at multiplied_out_eqn, 
  have tmp : (cubed f x) .+ (.- a) = myfld.zero, 
    rw h, exact myfld.add_negate a, 
  rw tmp at multiplied_out_eqn, clear tmp, clear h, 
  have h1 : x .+ (.- (fld_with_cube_root.cubrt a)) ≠ myfld.zero, 
    exact ne_diff_not_zero f x (fld_with_cube_root.cubrt a) x_not_one, 
  rw only_one_reciprocal f (two f) _ fld_not_char_two.not_char_two at x_not_root_a, clear x_not_one, 
  have h2 : (x .+ (.- ((fld_with_cube_root.cubrt a) .* (cubrt_unity_a f)))) ≠ myfld.zero, 
    exact ne_diff_not_zero f x ((fld_with_cube_root.cubrt a) .* (cubrt_unity_a f)) x_not_root_a, 
  clear x_not_root_a, 
  rw only_one_reciprocal f (two f) _ fld_not_char_two.not_char_two at x_not_root_b, 
  have h3 : (x .+ (.- ((fld_with_cube_root.cubrt a) .* (cubrt_unity_b f)))) ≠ myfld.zero, 
    exact ne_diff_not_zero f x ((fld_with_cube_root.cubrt a) .* (cubrt_unity_b f)) x_not_root_b, 
  clear x_not_root_b, 
  exact (mul_nonzero f _ _ (mul_nonzero f (x .+ _) _ h1 h2) h3) multiplied_out_eqn, 
end 

lemma cubrt_unity_nonzero (f : Type) [myfld f] [fld_not_char_two f] (rt_minus_three : f)
                      (rt_proof : rt_minus_three .* rt_minus_three = (.- (three f))) : 
              (cube_root_of_unity f rt_minus_three rt_proof) ≠ myfld.zero := 
begin 
  intros h, 
  have h1 : cubed f (cube_root_of_unity f rt_minus_three rt_proof) = myfld.zero, 
    rw h, unfold cubed, rw mul_zero f _, 
  rw cubrt_unity_correct f rt_minus_three rt_proof at h1, 
  exact myfld.zero_distinct_one h1, 
end 

/- We make the other cube roots explicit and give explicit proofs of their correctness. 
    This is tedious and a bit redundant, but it'll be useful later when we prove that a cubic has three solutions.-/ 

def alt_cubrt_a (f : Type) [myfld f] [fld_with_cube_root f] [fld_with_sqrt f] [fld_not_char_two f] (a : f) : f := 
        myfld.mul
          (cube_root_of_unity f (sqroot  (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f))))
          (fld_with_cube_root.cubrt a)

lemma alt_cubrt_a_nonzero (f : Type) [myfld f] [fld_with_cube_root f] [fld_with_sqrt f] [fld_not_char_two f] 
    (a : f) (a_ne_zero : a ≠ myfld.zero) : (alt_cubrt_a f a) ≠ myfld.zero := 
begin 
  unfold alt_cubrt_a, 
  exact mul_nonzero f (cube_root_of_unity f (sqroot  (.- (three f))) _) (fld_with_cube_root.cubrt a)
      (cubrt_unity_nonzero f (sqroot  (.- (three f))) _) (cubrt_nonzero f a a_ne_zero), 
end 

def alt_cubrt_b (f : Type) [myfld f] [fld_with_cube_root f] [fld_with_sqrt f] [fld_not_char_two f] (a : f) : f := 
        myfld.mul
          (cube_root_of_unity f (.- (sqroot  (.- (three f)))) (negative_sqrt f (.- (three f))))
          (fld_with_cube_root.cubrt a)

lemma alt_cubrt_b_nonzero (f : Type) [myfld f] [fld_with_cube_root f] [fld_with_sqrt f] [fld_not_char_two f] 
    (a : f) (a_ne_zero : a ≠ myfld.zero) : (alt_cubrt_b f a) ≠ myfld.zero := 
begin 
  unfold alt_cubrt_b, 
  exact mul_nonzero f (cube_root_of_unity f _ _) (fld_with_cube_root.cubrt a)
      (cubrt_unity_nonzero f (.- (sqroot  (.- (three f)))) _) (cubrt_nonzero f a a_ne_zero), 
end 

lemma three_cubrts (f : Type) [myfld f] [fld_not_char_two f] [fld_with_cube_root f] (rt_minus_three : f) (a : f)
                          (rt_proof : rt_minus_three .* rt_minus_three = (.- (three f))) : 
            (cubed f ((fld_with_cube_root.cubrt a) .* (cube_root_of_unity f rt_minus_three rt_proof))) = a := 
begin 
  rw cube_of_product f _ _, rw cubrt_unity_correct f rt_minus_three rt_proof, 
  rw cubrt_cubed f a, rw simp_mul_one f _, 
end 

lemma no_other_cubrts_simple (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_with_cube_root f] (a1 x : f) : 
    (x ≠ (fld_with_cube_root.cubrt a1)) -> 
    (x ≠ (alt_cubrt_a f a1)) -> 
    (x ≠ (alt_cubrt_b f a1)) -> 
    (cubed f x) ≠ a1 := 
begin 
  unfold alt_cubrt_a, unfold alt_cubrt_b, 
  have prev_version : (x ≠ (fld_with_cube_root.cubrt a1)) -> 
    (x ≠ (fld_with_cube_root.cubrt a1) .* (cubrt_unity_a f)) -> 
    (x ≠ (fld_with_cube_root.cubrt a1) .* (cubrt_unity_b f)) -> 
    (cubed f x) ≠ a1, 
    exact no_other_cubrts f a1 x, 
  unfold cubrt_unity_a at prev_version, unfold cubrt_unity_b at prev_version, 
  unfold cube_root_of_unity, rw myfld.mul_comm _ (fld_with_cube_root.cubrt _), 
  rw myfld.mul_comm _ (fld_with_cube_root.cubrt _), 
  exact prev_version, 
end 

lemma alt_cubrt_a_correct (f : Type) [myfld f] [fld_with_cube_root f] [fld_with_sqrt f] [fld_not_char_two f] (a : f) : 
        cubed f (alt_cubrt_a f a) = a := 
begin 
  unfold alt_cubrt_a, rw cube_of_product f _ _, rw cubrt_unity_correct f _, 
  rw one_mul_simp, rw cubrt_cubed f a, 
end 

lemma alt_cubrt_b_correct (f : Type) [myfld f] [fld_with_cube_root f] [fld_with_sqrt f] [fld_not_char_two f] (a : f) : 
        cubed f (alt_cubrt_b f a) = a := 
begin 
  unfold alt_cubrt_b, rw cube_of_product f _ _, rw cubrt_unity_correct f _, 
  rw one_mul_simp, rw cubrt_cubed f a, 
end 