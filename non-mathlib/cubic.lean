import field_definition
import field_results
import numbers
import roots
import quadratic

lemma multiply_out_cubed (f : Type) [myfld f] (x a : f) : 
    (cubed f (x .+ a)) = ((cubed f x) .+ (((three f) .* ((square f x) .* a)) .+ (((three f) .* ((x .* a) .* a)) .+ (cubed f a)))) := 
begin 
  unfold cubed, unfold three, unfold square, 
  repeat {rw distrib_simp f _ _ _}, repeat {rw distrib_simp_alt f _ _ _}, 
  rw one_mul_simp f _, rw myfld.mul_assoc _ _ _, 
  rw myfld.mul_comm a x, rw myfld.mul_assoc a x a, rw myfld.mul_comm a x, rw myfld.mul_assoc _ _ _, 
  rw myfld.mul_assoc a x x, rw myfld.mul_comm a x, rw <- myfld.mul_assoc x a x, rw myfld.mul_comm a x, 
  repeat {rw myfld.mul_assoc _ _ _}, repeat {rw <- myfld.add_assoc _ _ _}, 
  rw myfld.add_assoc ((x .* a) .* a) ((x .* x) .* a) _, 
  rw myfld.add_comm ((x .* a) .* a) ((x .* x) .* a), 
  repeat {rw <- myfld.add_assoc _ _ _}, rw one_mul_simp f _, 
end 

def cardano_intermediate_val (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_not_char_three f] 
        (c d : f) : f := 
  sqroot (((square f d) .* (myfld.reciprocal (four f) (four_ne_zero f))) .+ ((cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))))

def cardano_other_int_val (f : Type) [myfld f] [fld_not_char_two f] (d : f) : f := 
    .- (d .* (myfld.reciprocal (two f) fld_not_char_two.not_char_two))

/- Prove that (if c ≠ 0) the fraction in the Cardano formula is a legal fraction. 
  We do actually need a couple of versions of this for different purposes, so the formula is split over 
    a few different lemmae.-/ 

lemma cardano_den_not_zero_general (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_not_char_three f] 
  (c d : f) (c_ne_zero : c ≠ myfld.zero) : 
    (square f (cardano_intermediate_val f c d)) .+ (.- (square f (cardano_other_int_val f d))) ≠ myfld.zero := 
begin 
  intro h, 
  unfold square at h, unfold cardano_other_int_val at h, unfold cardano_intermediate_val at h, 
  rw fld_with_sqrt.sqrt_mul_sqrt _ at h, 
  rw mul_negate f _ at h, rw <- mul_negate_alt f _ at h, rw double_negative f _ at h, 
  rw <- myfld.mul_assoc d _ _ at h, rw myfld.mul_comm d (myfld.reciprocal (two f) _) at h, 
  rw myfld.mul_assoc (myfld.reciprocal (two f) _) (myfld.reciprocal (two f) _) _ at h, 
  rw mul_two_reciprocals f (two f) (two f) _ _ at h, 
  rw myfld.mul_comm _ d at h, rw myfld.mul_assoc d d _ at h, 
  unfold square at h, unfold four at h, 
  rw reciprocal_rewrite f ((two f) .+ (two f)) ((two f) .* (two f)) (two_plus_two f) _ at h, 
  rw myfld.add_comm (_ .* _) _ at h, rw <- myfld.add_assoc _ _ _ at h, 
  rw only_one_reciprocal f ((two f) .* (two f)) _ 
        (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two) at h, 
  rw myfld.add_negate _ at h, 
  rw zero_simp at h, 
  have h1 : (cubed f c) ≠ myfld.zero, 
    unfold cubed, exact mul_nonzero f c (c .* c) c_ne_zero (mul_nonzero f c c c_ne_zero c_ne_zero), 
  exact (mul_nonzero f (cubed f c) (myfld.reciprocal (twenty_seven f) _) h1 (reciprocal_ne_zero f (twenty_seven f) _)) h, 
end 


lemma cardano_den_not_zero_int (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_not_char_three f] 
        (c d : f) (c_ne_zero : c ≠ myfld.zero) : 
          (cardano_intermediate_val f c d) .+ (cardano_other_int_val f d) ≠ myfld.zero := 
begin 
  intro h, 
  have h1 : (((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) .* ((cardano_intermediate_val f c d) .+ (.- (cardano_other_int_val f d)))) = 
                      myfld.zero, 
    rw h, rw mul_zero f _, clear h, rename h1 h, 
  rw difference_of_squares f _ _ at h, 
  exact cardano_den_not_zero_general f c d c_ne_zero h, 
end 

lemma cardano_den_not_zero_int_alt (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_not_char_three f] 
        (c d : f) (c_ne_zero : c ≠ myfld.zero) : 
          (cardano_intermediate_val f c d) .+ (.- (cardano_other_int_val f d)) ≠ myfld.zero := 
begin 
  intro h, 
  have h1 : (((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) .* ((cardano_intermediate_val f c d) .+ (.- (cardano_other_int_val f d)))) = 
                      myfld.zero, 
    rw h, rw zero_mul f _, clear h, rename h1 h, 
  rw difference_of_squares f _ _ at h, 
  exact cardano_den_not_zero_general f c d c_ne_zero h, 
end 

lemma cardano_denominator_not_zero (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_not_char_three f] [fld_with_cube_root f] 
        (c d : f) (c_ne_zero : c ≠ myfld.zero) (cubrt_func : f -> f)
      (cubrt_func_nonzero : ∀ (x : f), x ≠ myfld.zero -> (cubrt_func x ≠ myfld.zero)) : 
  (cubrt_func ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) .* (three f)
       ≠ myfld.zero := 
begin 
  exact mul_nonzero f _ (three f) (cubrt_func_nonzero _ (cardano_den_not_zero_int f c d c_ne_zero)) fld_not_char_three.not_char_three, 
end 

/- This is the formula, finally. Note that we are intentionally vague about the cube root - any 
   function that gives a cube root can be provided. This is so that we can easily create a proof 
   that covers all three cube roots at the same time.-/ 
 def cardano_formula (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d : f) (c_ne_zero : c ≠ myfld.zero) (cubrt_func : f -> f)
      (cubrt_func_nonzero : ∀ (x : f), x ≠ myfld.zero -> (cubrt_func x ≠ myfld.zero))
      (cubrt_func_correct : ∀ (x : f), (cubed f (cubrt_func x)) = x) : f := 
  ((cubrt_func ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) .+ (.- (c .* (myfld.reciprocal ((cubrt_func ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) .* (three f)) (cardano_denominator_not_zero f c d c_ne_zero cubrt_func cubrt_func_nonzero)))))

def depressed_cubic_subst (f : Type) [myfld f] (c d x : f) : f := 
  (cubed f x) .+ ((c .* x) .+ d)

/- This is now the proof that all depressed cubics can be solved by the above formula. We're not doing 
    uniqueness yet.-/ 
lemma cardano_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d : f) (c_ne_zero : c ≠ myfld.zero) (cubrt_func : f -> f)
      (cubrt_func_nonzero : ∀ (x : f), x ≠ myfld.zero -> (cubrt_func x ≠ myfld.zero))
      (cubrt_func_correct : ∀ (x : f), (cubed f (cubrt_func x)) = x) : 
          depressed_cubic_subst f c d (cardano_formula f c d c_ne_zero cubrt_func cubrt_func_nonzero cubrt_func_correct)
                 = myfld.zero := 
begin 
  /- First multiply out the brackets.-/ 
  unfold depressed_cubic_subst, unfold cardano_formula, 
  rw distrib_simp_alt f c _ _, rw multiply_out_cubed f _ _, unfold square, 
  rw cubrt_func_correct _, rw cube_of_negative f _, 
  simp only [mul_negate, mul_negate_alt_simp, double_negative], 

  /- Now simplify two terms where we have 3 * 1/3.-/ 
  rw split_reciprocal f _ (three f) _, rw myfld.mul_comm (myfld.reciprocal _ _) (myfld.reciprocal (three f) _), 
  rw myfld.mul_assoc c (myfld.reciprocal (three f) _) _, 
  rw myfld.mul_comm c (myfld.reciprocal (three f) _), 
  rw myfld.mul_comm _ (((myfld.reciprocal (three f) _) .* c) .* (myfld.reciprocal _ _)), 
  rw myfld.mul_comm _ (((myfld.reciprocal (three f) _) .* c) .* (myfld.reciprocal _ _)), 
  repeat {rw myfld.mul_assoc _ _ _}, 
  rw myfld.mul_reciprocal (three f) _, rw one_mul_simp f _, 

  /- There are also some points where we have cubrt (stuff) * reciprocal (cubrt (stuff)) . 
      So these also simplify.-/ 
  rw <- myfld.mul_assoc c (myfld.reciprocal (cubrt_func _) _) (cubrt_func _), 
  rw myfld.mul_comm (myfld.reciprocal (cubrt_func _) _) (cubrt_func _), 
  rw myfld.mul_reciprocal _ _, rw simp_mul_one f _, 

  /- We can now cancel some of the terms by moving them next to their negations. -/ 
  rw myfld.add_comm (c .* _) (.- _), 
  rw myfld.add_comm (((c .* _) .* c) .* _) (.- (cubed f _)), 
  repeat {rw <- myfld.add_assoc _ _ _}, 
  rw myfld.add_assoc (((c .* _) .* c) .* _) (.- _) _, 
  rw myfld.add_negate _, rw simp_zero f _, 
  rw myfld.add_comm (.- _) _, rw myfld.add_comm _ d, 
  repeat {rw <- myfld.add_assoc _ _ _}, 
  rw myfld.add_negate _, rw zero_simp f _, 

  /- One of our remaining terms has two reciprocals multiplied together. Also, it is 
     the cube of some stuff multiplied by a cube root, so we can remove the cube root from the expression.-/ 
  rw myfld.mul_comm (myfld.reciprocal _ _) c, 
  rw <- myfld.mul_assoc c (myfld.reciprocal _ _) (myfld.reciprocal _ _), 
  repeat {rw cube_of_product f _ _}, rw cube_of_reciprocal f (cubrt_func _), 
  rw reciprocal_rewrite f (cubed f (cubrt_func _)) _ (cubrt_func_correct _) _, 
  rw cube_of_reciprocal f _, 

  /- We now have the reciprocal of (cardano_intermediate_val + cardano_other_int_val) . 
  cardano_intermediate_val is a square root, so in the interest of rationalising denominators 
   we can multiply this by (int_val - other_int_val) / (int_val - other_int_val) . -/ 
  rw only_one_reciprocal f ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) _ (cardano_den_not_zero_int f c d c_ne_zero), 
  have tmp : (((cardano_intermediate_val f c d) .+ (.- (cardano_other_int_val f d))) .* (myfld.reciprocal ((cardano_intermediate_val f c d) .+ (.- (cardano_other_int_val f d))) (cardano_den_not_zero_int_alt f c d c_ne_zero)))
                  = myfld.one, 
    rw myfld.mul_reciprocal _ _, 
  have tmp2 : (myfld.reciprocal ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) (cardano_den_not_zero_int f c d c_ne_zero))
              = ((myfld.reciprocal ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) (cardano_den_not_zero_int f c d c_ne_zero)) .* myfld.one), 
    exact myfld.mul_one _, 
  rw <- tmp at tmp2, clear tmp, rename tmp2 tmp, 
  rw myfld.mul_comm _ (myfld.reciprocal _ _) at tmp, 
  rw myfld.mul_assoc (myfld.reciprocal _ _) (myfld.reciprocal _ _) _ at tmp, 
  rw mul_two_reciprocals f _ _ _ _ at tmp, 
  rw reciprocal_rewrite f _ _ (difference_of_squares f _ _) _ at tmp, 
  rw tmp, clear tmp, 

  /- Now that we've pre-rationalized the denominator, it's finally time to unfold these intermediate values.-/ 
  unfold cardano_intermediate_val, unfold cardano_other_int_val, 

  /- Our fraction now has an expression on the bottom that simplifies to p^3/27. 
     Because reciprocals need to have a proof that the denominator isn't zero, it's easier 
     to do this in a sub-proof so that the reciprocal only needs to be rewritten once.-/ 
  have denominator_sub_proof : 
    ((square f (sqroot (((square f d) .* (myfld.reciprocal (four f) _)) .+ ((cubed f c) .* (myfld.reciprocal (twenty_seven f) _))))) .+ (.- (square f (.- (d .* (myfld.reciprocal (two f) fld_not_char_two.not_char_two)))))) = 
    ((cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))), 

    rw sqrt_squared f _, unfold square, 
    rw mul_negate f _ _, rw double_negative f _, rw mul_negate_alt_simp f _ _, 
    rw <- myfld.mul_assoc d (myfld.reciprocal _ _) (_ .* _), 
    rw myfld.mul_comm d (myfld.reciprocal _ _), 
    rw myfld.mul_assoc (myfld.reciprocal _ _) (myfld.reciprocal _ _) d, 
    rw mul_two_reciprocals f (two f) (two f) _ _, 
    rw myfld.mul_comm (myfld.reciprocal _ _) d, rw myfld.mul_assoc d d _, 
    rw myfld.add_comm _ (.- _), rw myfld.add_assoc _ _ _, 
    unfold four, 
    rw reciprocal_rewrite f ((two f) .+ (two f)) ((two f) .* (two f)) (two_plus_two _) _, 
    rw only_one_reciprocal f ((two f) .* (two f)) _ (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two), 
    rw myfld.add_comm (.- _) _, 
    rw myfld.add_negate _, rw simp_zero f _, 

  /- And now we can do the rewrite in the main proof.-/ 
  rw reciprocal_rewrite f _ _ denominator_sub_proof _, 

  /- The big fraction is now reduced to p^3 (stuff) / (27 (p^3/27)) . 
      A bit of cancellation will reduce that to the part abbreviated "stuff" in that equation.-/ 
  rw myfld.mul_assoc (myfld.reciprocal _ _) (myfld.reciprocal _ _) (_ .+ _), 
  rw myfld.mul_comm (myfld.reciprocal (cubed f (three f)) _) (myfld.reciprocal (_ .* _) _), 
  repeat {rw <- myfld.mul_assoc _ _ _}, repeat {rw myfld.mul_assoc _ _ _}, 
  rw split_reciprocal f (cubed f c) _ _, 
  rw myfld.mul_assoc (cubed f c) (myfld.reciprocal (cubed f c) _) _, 
  rw myfld.mul_reciprocal (cubed f c), rw one_mul_simp f _, 
  rw double_reciprocal f _, 
  rw reciprocal_rewrite f (cubed f (three f)) (twenty_seven f) (three_cubed f) _, 
  rw myfld.mul_reciprocal (twenty_seven f) _, rw one_mul_simp f _, 

  /- And now one of the big square roots is positive and one is negative, so they cancel.-/ 
  clear denominator_sub_proof, 
  repeat {rw add_negate f _ _}, rw double_negative f _, 
  rw <- myfld.add_assoc (.- (sqroot _)) _ _, 
  rw myfld.add_assoc _ (.- (sqroot _)) _, 
  rw myfld.add_comm _ (.- (sqroot _)), 
  repeat {rw <- myfld.add_assoc _ _ _}, repeat {rw myfld.add_assoc _ _ _}, /- TODO: improve this line-/ 
  rw myfld.add_negate _, rw simp_zero f _, 

  /- And finally we have (-d/2) + (-d/2) + d, which is obviously zero.-/ 
  rw <- add_negate f (d .* _) (d .* _), 
  rw <- distrib_simp_alt f d _ _, 
  rw only_one_reciprocal f (two f) _ (two_ne_zero f), 
  rw add_two_halves f, rw <- myfld.mul_one d, 
  rw myfld.add_comm (.- d) d, 
  exact myfld.add_negate d, 
end 

def cardano_formula_a (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d : f) (c_ne_zero : c ≠ myfld.zero) : f := 
  cardano_formula f c d c_ne_zero fld_with_cube_root.cubrt (cubrt_nonzero f) (cubrt_cubed f)

def cardano_formula_b (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d : f) (c_ne_zero : c ≠ myfld.zero) : f := 
  cardano_formula f c d c_ne_zero (alt_cubrt_a f) (alt_cubrt_a_nonzero f) (alt_cubrt_a_correct f)

def cardano_formula_c (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d : f) (c_ne_zero : c ≠ myfld.zero) : f := 
  cardano_formula f c d c_ne_zero (alt_cubrt_b f) (alt_cubrt_b_nonzero f) (alt_cubrt_b_correct f)

/- And as we have proven that all versions of the cardano_formula are correct when substituted into the equation, all three 
of the above formulae are solutions to a depressed cubic equation.-/ 

def depressed_cubic_solution_c_zero (f : Type) [myfld f] 
     (c d : f) (c_eq_zero : c = myfld.zero) (cubrt_func : f -> f)
      (cubrt_func_correct : ∀ (x : f), (cubed f (cubrt_func x)) = x) : 
     f := .- (cubrt_func (d))

lemma depressed_cubic_solution_c_zero_correct (f : Type) [myfld f] 
    (c d : f) (c_eq_zero : c = myfld.zero) (cubrt_func : f -> f)
      (cubrt_func_correct : ∀ (x : f), (cubed f (cubrt_func x)) = x) : 
  depressed_cubic_subst f c d 
    (depressed_cubic_solution_c_zero f c d c_eq_zero cubrt_func cubrt_func_correct)
                 = myfld.zero := 
begin 
  unfold depressed_cubic_solution_c_zero, unfold depressed_cubic_subst, 
  rw c_eq_zero, rw mul_zero f _, rw simp_zero f _, 
  unfold cubed, repeat {rw mul_negate f _ _}, repeat {rw mul_negate_alt_simp f _ _}, rw double_negative f _, 
  rw myfld.mul_assoc _ _ _, unfold cubed at cubrt_func_correct, rw <- myfld.mul_assoc, 
  rw cubrt_func_correct _, 
  rw myfld.add_comm, rw myfld.add_negate d, 
end 

def depressed_cubic_solution_c_zero_a (f : Type) [myfld f] [fld_with_cube_root f] 
  (c d : f) (c_eq_zero : c = myfld.zero) : f := 
    depressed_cubic_solution_c_zero f c d c_eq_zero fld_with_cube_root.cubrt (cubrt_cubed f)

def depressed_cubic_solution_c_zero_b (f : Type) [myfld f] [fld_with_cube_root f] [fld_with_sqrt f] [fld_not_char_two f] 
  (c d : f) (c_eq_zero : c = myfld.zero) : f := 
    depressed_cubic_solution_c_zero f c d c_eq_zero (alt_cubrt_a f) (alt_cubrt_a_correct f)

def depressed_cubic_solution_c_zero_c (f : Type) [myfld f] [fld_with_cube_root f] [fld_with_sqrt f] [fld_not_char_two f] 
  (c d : f) (c_eq_zero : c = myfld.zero) : f := 
    depressed_cubic_solution_c_zero f c d c_eq_zero (alt_cubrt_b f) (alt_cubrt_b_correct f)

/- This is a bit lame, I will admit. We have a formula that is proven to be correct when c is 
    zero, and a formula that is proven to be correct when c is not zero. I don't right now see that we can merge them 
    into one formula, however, because while Lean does have a "cond" operator that functions 
    like the ternary operator in most languages, it doesn't seem to allow for accessing a proof 
    of the proposition that has been evaluated. Ergo, we can't use it here because calling the 
    "c is not zero" version of the formula requires that we have a proof that c is not zero.-/ 

def cubic_subst (f : Type) [myfld f] (a b c d x : f) : f := 
  (a .* (cubed f x)) .+ ((b .* (square f x)) .+ ((c .* x) .+ d))

/- This is a fairly trivial result, but it enables us to create a simplified version of the formula with 
   no x^3 coefficient.-/ 
lemma divide_cubic_through (f : Type) [myfld f] (a b c d x : f) (a_ne_zero : a ≠ myfld.zero) : 
      (cubic_subst f a b c d x) = myfld.zero <-> 
      (cubic_subst f myfld.one (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) x)
       = myfld.zero := 
begin 
  unfold cubic_subst, split, intros h, 
  have h1 : (((a .* (cubed f x)) .+ ((b .* (square f x)) .+ ((c .* x) .+ d))) .* (myfld.reciprocal a a_ne_zero)) = myfld.zero, 
    rw h, exact mul_zero f _, 
  clear h, rename h1 h, 
  repeat {rw distrib_simp f _ _ _ at h}, 
  repeat {rw <- myfld.mul_assoc _ _ (myfld.reciprocal a a_ne_zero) at h}, 
  repeat {rw myfld.mul_comm _ (myfld.reciprocal a a_ne_zero) at h}, 
  rw myfld.mul_assoc a (myfld.reciprocal a a_ne_zero) _ at h, 
  rw myfld.mul_reciprocal a a_ne_zero at h, 
  rw myfld.mul_comm d (myfld.reciprocal a a_ne_zero), 
  repeat {rw myfld.mul_assoc _ _ _ at h}, repeat {rw myfld.mul_assoc _ _ _}, 
  exact h, 

  intros h, 
  have h1 : (((myfld.one .* (cubed f x)) .+ (((b .* (myfld.reciprocal a a_ne_zero)) .* (square f x)) .+ (((c .* (myfld.reciprocal a a_ne_zero)) .* x) .+ (d .* (myfld.reciprocal a a_ne_zero))))) .* a) = myfld.zero, 
    rw h, exact mul_zero f _, 
  clear h, rename h1 h, 
  repeat {rw distrib_simp f _ _ _ at h}, 
  rw <- myfld.mul_assoc _ (myfld.reciprocal a a_ne_zero) a at h, 
  rw myfld.mul_comm (myfld.reciprocal a a_ne_zero) a at h, rw myfld.mul_reciprocal a a_ne_zero at h, rw simp_mul_one at h, 
  repeat {rw <- myfld.mul_assoc _ _ a at h}, repeat {rw myfld.mul_comm _ a at h}, 
  repeat {rw myfld.mul_assoc _ a _ at h}, repeat {rw <- myfld.mul_assoc _ _ a at h}, 
  repeat {rw myfld.mul_comm (myfld.reciprocal a a_ne_zero) a at h}, 
  rw myfld.mul_reciprocal a a_ne_zero at h, 
  repeat {rw simp_mul_one at h}, rw one_mul_simp at h, 
  exact h, 
end 

def third (f : Type) [myfld f] [fld_not_char_three f] : f := 
  (myfld.reciprocal (three f) fld_not_char_three.not_char_three)

def twenty_seventh (f : Type) [myfld f] [fld_not_char_three f] : f := 
  (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))

/- This looks weird and pointless but it simplifies a proof later.-/ 
lemma depressed_cubic_equal_split (f : Type) [myfld f] (c1 d1 c2 d2 x : f) : 
  (c1 = c2) /\ (d1 = d2) -> (depressed_cubic_subst f c1 d1 x) = (depressed_cubic_subst f c2 d2 x) := 
begin 
  intros h, cases h with h1 h2, rw h1, rw h2, 
end 

/- This is used in the next proof (reduce_cubic_to_depressed) . It could have been done with a "have", 
but the next proof is long enough that my computer was struggling with it, so it seemed worth moving this bit out.-/ 
lemma helper_bcubed (f : Type) [myfld f] [fld_not_char_three f] (b : f) : 
(b .* ((third f) .* (b .* ((third f) .* b)))) = 
          ((three f) .* ((myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f)) .* ((b .* b) .* b))) := 
begin 
  unfold third, unfold twenty_seven, unfold nine, rw split_reciprocal f _ _ _, 
  rw <- myfld.mul_assoc (myfld.reciprocal (three f) _), 
  rw myfld.mul_assoc (three f) (myfld.reciprocal (three f) _) _, 
  rw myfld.mul_reciprocal (three f) _, rw one_mul_simp f _, 
  repeat {rw myfld.mul_comm b (_ .* _) }, 
  repeat {rw myfld.mul_assoc _ _ _}, rw mul_two_reciprocals f _ _ _ _, 
end 

/- Ditto.-/ 
lemma helper_twothirds (f : Type) [myfld f] [fld_not_char_three f] : 
    ((.- (third f)) .+ myfld.one) = (third f) .+ (third f) := 
begin 
  have h : myfld.one = (third f) .* (three f) , 
    unfold third, rw myfld.mul_comm, symmetry, exact myfld.mul_reciprocal (three f) _, 
  rw h, clear h, 
  have h : (.- (third f)) = (third f) .* (.- myfld.one) , 
    rw <- mul_negate_alt f _ _, rw simp_mul_one f _, 
  rw h, clear h, 
  rw <- distrib_simp_alt f _ _ _, unfold third, unfold three, 
  rw myfld.add_assoc (.- myfld.one) myfld.one _, 
  rw myfld.add_comm (.- myfld.one) myfld.one, rw myfld.add_negate myfld.one, 
  rw simp_zero f _, 
  rw distrib_simp_alt f _ _ _, rw simp_mul_one f _, 
end 

lemma reduce_cubic_to_depressed (f : Type) [myfld f] [fld_not_char_three f] (b c d x y : f) : 
    x = y .+ (.- (b .* (third f))) -> 
    (cubic_subst f myfld.one b c d x) = 
    (depressed_cubic_subst f (((square f b) .* (.- (third f))) .+ c) ((twenty_seventh f) .* ((((two f) .* (cubed f b)) .+ (.- ((nine f) .* (b .* c)))) .+ ((twenty_seven f) .* d))) y) := 
begin 
  intros h, rw h, clear h, unfold cubic_subst, 
  rw multiply_out_cubed f y _, rw multiply_out_squared f _ _, 
  rw one_mul_simp f _, 
  repeat {rw distrib_simp_alt f _ _ _}, 
  rw mul_negate f _ _, repeat {rw mul_negate_alt_simp f _ _}, repeat {rw mul_negate f _ _}, rw mul_negate_alt_simp f _ _, 
  rw double_negative f _, 

  /- First job is to cancel the terms that have 3 * (1/3) in them.-/ 
  have third_three : (three f) .* (third f) = myfld.one, 
    unfold third, rw myfld.mul_reciprocal (three f) _, 
  rw myfld.mul_comm b (third f), rw myfld.mul_assoc _ (third f) _, 
  rw myfld.mul_comm _ (third f), rw <- myfld.mul_assoc (third f) _ _, 
  rw myfld.mul_assoc y (third f) b, rw myfld.mul_comm y (third f), 
  rw <- myfld.mul_assoc (third f) y b, rw <- myfld.mul_assoc (third f) (y .* b) _, 
  repeat {rw myfld.mul_assoc (three f) (third f) _}, 
  rw third_three, clear third_three, 
  repeat {rw one_mul_simp f _}, 

  /- Now we have a term for by^2 and -by^2, so these cancel.-/ 
  unfold square, rw myfld.mul_comm b (y .* y), 
  rw myfld.add_comm (.- ((y .* y) .* b)) _, 
  repeat {rw <- myfld.add_assoc}, 
  rw myfld.add_assoc (.- ((y .* y) .* b)) ((y .* y) .* b) _, 
  rw myfld.add_comm (.- ((y .* y) .* b)) ((y .* y) .* b), 
  rw myfld.add_negate ((y .* y) .* b), rw simp_zero, 

  /- This ultimately needs to be made equivalent to the depressed cubic formula, so we gather all the 
      terms that are multiplied by y together.-/ 
  rw myfld.mul_comm _ y, 
  repeat {rw myfld.mul_assoc _ y _, rw myfld.mul_comm _ y}, 
  rw <- myfld.mul_assoc y (two f) _, rw myfld.mul_assoc _ y _, rw myfld.mul_comm b y, repeat {rw <- myfld.mul_assoc y b _}, 
  rw mul_negate_alt f y _, rw myfld.mul_comm c y, 
  rw myfld.add_assoc (cubed f (.- ((third f) .* b))) (y .* _) _, 
  rw myfld.add_comm _ (y .* (.- (b .* ((two f) .* ((third f) .* b))))), 
  rw <- myfld.add_assoc (y .* (.- (b .* ((two f) .* ((third f) .* b))))) _ _, 
  rw myfld.add_assoc (y .* _) (y .* _), 
  rw <- distrib_simp_alt f y _ _, 
  rw myfld.add_assoc _ (y .* c) _, rw myfld.add_comm _ (y .* c), rw <- myfld.add_assoc (y .* c) _ _, 
  rw myfld.add_assoc _ (y .* c) _, rw myfld.add_comm _ (y .* c), rw <- myfld.add_assoc (y .* c) _ _, 
  rw myfld.add_assoc _ (y .* c) _, 
  rw <- distrib_simp_alt f y _ c, 

  /- We can now fold this back into the depressed cubic formula, 
      which will make the remaining algebra slightly easier to follow.-/ 
  rw myfld.mul_comm y _, 
  /- The following line is ugly, but it's just a copy-paste of the algebra in the sidebar.-/ 
  have tmp : (cubed f y) .+ (((((b .* ((third f) .* b)) .+ (.- (b .* ((two f) .* ((third f) .* b))))) .+ c) .* y) .+ ((cubed f (.- ((third f) .* b))) .+ ((b .* ((.- ((third f) .* b)) .* (.- ((third f) .* b)))) .+ ((.- (c .* ((third f) .* b))) .+ d))))
      = 
      depressed_cubic_subst f (((b .* ((third f) .* b)) .+ (.- (b .* ((two f) .* ((third f) .* b))))) .+ c) ((cubed f (.- ((third f) .* b))) .+ ((b .* ((.- ((third f) .* b)) .* (.- ((third f) .* b)))) .+ ((.- (c .* ((third f) .* b))) .+ d))) y, 
    unfold depressed_cubic_subst, 
  rw tmp, clear tmp, 

  /- This enables us to break down into two goals (one for the y term and one for the constant.) -/ 
  apply depressed_cubic_equal_split f _ _ _ _ y, split, 

  /- (b^2) /3 - 2 (b/^2) 3 = - (b^2) /3, which solves the y term goal.-/ 
  rw myfld.mul_comm _ b, rw myfld.mul_comm _ (b .* _), rw myfld.mul_assoc _ b _, 
  rw myfld.mul_comm (two f) b, rw <- myfld.mul_assoc b (two f) _, 
  rw myfld.mul_comm (b .* (third f)) b, repeat {rw myfld.mul_assoc b b _}, 
  rw mul_negate_alt f (b .* b) _, 
  rw <- distrib_simp_alt f (b .* b) _ _, 
  rw myfld.mul_comm (two f) (third f), 
  have tmp : (third f) = ((third f) .* myfld.one), 
    exact myfld.mul_one (third f), 
  rewrite [tmp] {occs := occurrences.pos [1]}, clear tmp, 
  rw mul_negate_alt f (third f) (two f), 
  rw <- distrib_simp_alt f (third f) _ _, 
  have tmp : myfld.one .+ (.- (two f)) = .- (myfld.one), 
    unfold two, rw add_negate f myfld.one myfld.one, 
    rw myfld.add_assoc myfld.one (.- myfld.one) (.- myfld.one), 
    rw myfld.add_negate myfld.one, rw <- zero_add f (.- myfld.one), 
  rw tmp, clear tmp, 
  rw <- mul_negate_alt f (third f) myfld.one, rw simp_mul_one f _, 
  rw <- mul_negate_alt f (b .* b) (third f), 

  /- The constant goal is a bit more complicated, but all it really involves is collecting together the b^3 terms 
       and reducing the coefficient of each term to a single power of three.-/ 
  unfold cubed, repeat {rw mul_negate f _ _}, repeat {rw mul_negate_alt_simp f _ _}, 
  repeat {rw double_negative f _}, 
  rw myfld.mul_assoc (twenty_seventh f) (twenty_seven f) _, 
  rw myfld.mul_comm (twenty_seventh f) (twenty_seven f), unfold twenty_seventh, 
  rw myfld.mul_reciprocal (twenty_seven f) _, rw one_mul_simp f _, 
  rw myfld.mul_assoc (myfld.reciprocal (twenty_seven f) _) (nine f), 
  rw only_one_reciprocal f (twenty_seven f) _ (twenty_seven_ne_zero f), 
  have tmp : ((myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f)) .* (nine f)) = 
                (myfld.reciprocal (three f) fld_not_char_three.not_char_three), 
    unfold twenty_seven, unfold nine, rw split_reciprocal f _ _ _, rw split_reciprocal f _ _ _, 
    repeat {rw <- myfld.mul_assoc _ _ _}, rw myfld.mul_assoc (myfld.reciprocal _ _) (three f) _, 
    rw myfld.mul_comm (myfld.reciprocal (three f) _) (three f), 
    rw myfld.mul_reciprocal (three f) _, rw one_mul_simp f _, 
    rw myfld.mul_comm (myfld.reciprocal (three f) _) (three f), 
    rw myfld.mul_reciprocal (three f) _, rw simp_mul_one f _, 
  rw myfld.mul_assoc (myfld.reciprocal (twenty_seven f) _) (nine f) _, 
  rw tmp, clear tmp, 
  rw myfld.mul_assoc _ (two f) _, rw myfld.mul_comm _ (two f), rw <- myfld.mul_assoc (two f) _ _, 
  unfold two, rw distrib_simp f myfld.one myfld.one _, rw one_mul_simp f _, 
  rw myfld.add_assoc _ (b .* ((third f) .* (b .* ((third f) .* b)))) _, 
  rw helper_bcubed f b, 
  have tmp : ((three f) .* ((myfld.reciprocal (twenty_seven f) _) .* ((b .* b) .* b))) = 
    (myfld.one .* ((three f) .* ((myfld.reciprocal (twenty_seven f) _) .* ((b .* b) .* b)))), 
    rw one_mul_simp f _, 
  rewrite [tmp] {occs := occurrences.pos [2]}, clear tmp, 
  rw <- mul_negate f (third f) _, rw <- distrib_simp f _ _ _, rw helper_twothirds f, 
  rw distrib_simp f (third f) (third f) _, 
  rw myfld.mul_assoc (third f) (three f) _, 
  have tmp : (third f) .* (three f) = myfld.one, 
    unfold third, rw myfld.mul_comm _ _, rw myfld.mul_reciprocal (three f) _, 
  rw tmp, rw one_mul_simp f _, clear tmp, 
  rw myfld.mul_assoc c (third f) b, rw myfld.mul_comm c (third f), rw <- myfld.mul_assoc (third f) c b, 
  rw myfld.mul_comm c b, 
  rw myfld.mul_assoc b b b, 
  unfold third, 
end

/- We have now proven that every cubic equation can be reduced to a cubic equation 
    where the x^3 coefficient is 1, that every such cubic can be reduced to a depressed cubic, and 
    that every depressed cubic can be solved with Cardano's formula. This is therefore enough for a solution 
    to any general cubic. 
    The one wrinkle in this is that the Cardano formula only works if the x term is not 
    equal to zero. If the x term is equal to zero then the solution is trivial 
    (x just equals zero minus the cube root of the constant), but this cannot be 
    represented as part of the same formula using our notion of reciprocals. 
    Ergo, to get a general cubic formula we need to assume that it is always decidable whether 
    a value is zero or not.-/ 

lemma int_quantity_ne_zero_simp (f : Type) [myfld f] [fld_not_char_three f] (a1 b c : f) (a_ne_zero : a1 ≠ myfld.zero) : 
  ((three f) .* (a1 .* c)) .+ (.- (square f b)) ≠ myfld.zero -> 
  (((square f (b .* (myfld.reciprocal a1 a_ne_zero))) .* (.- (third f))) .+ (c .* (myfld.reciprocal a1 a_ne_zero))) ≠ myfld.zero := 
begin 
  intros h1 h2, 
  unfold square at h2, rw myfld.mul_comm _ (.- _) at h2, 
  repeat {rw myfld.mul_assoc _ _ (myfld.reciprocal a1 a_ne_zero) at h2}, 
  rw <- distrib_simp f _ _ _ at h2, rw <- mul_zero_by_reciprocal f a1 _ _ at h2, 
  rw mul_both_sides f _ _ (three f) at h2, rw mul_zero at h2, 
  rw distrib_simp at h2, repeat {rw mul_negate at h2}, rw myfld.mul_comm (_ .* _) (three f) at h2, 
  rw myfld.mul_assoc (three f) (third f) _ at h2, 
  unfold third at h2, rw myfld.mul_reciprocal (three f) _ at h2, rw one_mul_simp at h2, 
  rw mul_both_sides f _ _ a1 at h2, rw distrib_simp at h2, rw mul_zero at h2, rw mul_negate at h2, 
  rw myfld.mul_comm _ b at h2, repeat {rw <- myfld.mul_assoc at h2}, 
  rw myfld.mul_comm _ a1 at h2, rw myfld.mul_reciprocal a1 _ at h2, rw simp_mul_one at h2, 

  unfold square at h1, rw myfld.mul_comm c _ at h2, rw myfld.mul_assoc at h1, rw myfld.add_comm at h1, 
  cc, cc, exact fld_not_char_three.not_char_three, 
end 

def cubic_formula_a (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) (int_quantity_ne_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) ≠ myfld.zero) : f 
  := ((cardano_formula_a f (((square f (b .* (myfld.reciprocal a a_ne_zero))) .* (.- (third f))) .+ (c .* (myfld.reciprocal a a_ne_zero))) ((twenty_seventh f) .* ((((two f) .* (cubed f (b .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((nine f) .* ((b .* (myfld.reciprocal a a_ne_zero)) .* (c .* (myfld.reciprocal a a_ne_zero)))))) .+ ((twenty_seven f) .* (d .* (myfld.reciprocal a a_ne_zero))))) (int_quantity_ne_zero_simp f a b c a_ne_zero int_quantity_ne_zero)) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))))

lemma cubic_formula_a_correct (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] 
                                         [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) 
                (int_quantity_ne_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) ≠ myfld.zero) : 
    cubic_subst f a b c d (cubic_formula_a f a b c d a_ne_zero int_quantity_ne_zero) = myfld.zero := 
begin 
  rw divide_cubic_through f a b c d _ a_ne_zero, 
  have tmp : (cubic_formula_a f a b c d a_ne_zero int_quantity_ne_zero)
              = (((cubic_formula_a f a b c d a_ne_zero int_quantity_ne_zero) .+ ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f)))), 
    simp, 
  rw reduce_cubic_to_depressed f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (cubic_formula_a f a b c d a_ne_zero int_quantity_ne_zero) ((cubic_formula_a f a b c d a_ne_zero int_quantity_ne_zero) .+ ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))) tmp, 
  clear tmp, unfold cubic_formula_a, unfold cardano_formula_a, 
  rw <- myfld.add_assoc (cardano_formula f _ _ _ _ _ _) (.- _) _, 
  rw myfld.add_comm (.- _) _, rw myfld.add_negate _, rw zero_simp f _, 
  exact cardano_works f _ _ _ _ _ _, 
end 

def cubic_formula_b (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) (int_quantity_ne_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) ≠ myfld.zero) : f 
  := ((cardano_formula_b f (((square f (b .* (myfld.reciprocal a a_ne_zero))) .* (.- (third f))) .+ (c .* (myfld.reciprocal a a_ne_zero))) ((twenty_seventh f) .* ((((two f) .* (cubed f (b .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((nine f) .* ((b .* (myfld.reciprocal a a_ne_zero)) .* (c .* (myfld.reciprocal a a_ne_zero)))))) .+ ((twenty_seven f) .* (d .* (myfld.reciprocal a a_ne_zero))))) (int_quantity_ne_zero_simp f a b c a_ne_zero int_quantity_ne_zero)) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))))

lemma cubic_formula_b_correct (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] 
                                         [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) 
                (int_quantity_ne_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) ≠ myfld.zero) : 
    cubic_subst f a b c d (cubic_formula_b f a b c d a_ne_zero int_quantity_ne_zero) = myfld.zero := 
begin 
  rw divide_cubic_through f a b c d _ a_ne_zero, 
  have tmp : (cubic_formula_b f a b c d a_ne_zero int_quantity_ne_zero)
              = (((cubic_formula_b f a b c d a_ne_zero int_quantity_ne_zero) .+ ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f)))), 
    simp,
  rw reduce_cubic_to_depressed f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (cubic_formula_b f a b c d a_ne_zero int_quantity_ne_zero) ((cubic_formula_b f a b c d a_ne_zero int_quantity_ne_zero) .+ ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))) tmp, 
  clear tmp, unfold cubic_formula_b, unfold cardano_formula_b, 
  rw <- myfld.add_assoc (cardano_formula f _ _ _ _ _ _) (.- _) _, 
  rw myfld.add_comm (.- _) _, rw myfld.add_negate _, rw zero_simp f _, 
  exact cardano_works f _ _ _ _ _ _, 
end 

def cubic_formula_c (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) (int_quantity_ne_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) ≠ myfld.zero) : f 
  := ((cardano_formula_c f (((square f (b .* (myfld.reciprocal a a_ne_zero))) .* (.- (third f))) .+ (c .* (myfld.reciprocal a a_ne_zero))) ((twenty_seventh f) .* ((((two f) .* (cubed f (b .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((nine f) .* ((b .* (myfld.reciprocal a a_ne_zero)) .* (c .* (myfld.reciprocal a a_ne_zero)))))) .+ ((twenty_seven f) .* (d .* (myfld.reciprocal a a_ne_zero))))) (int_quantity_ne_zero_simp f a b c a_ne_zero int_quantity_ne_zero)) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f)))) 

lemma cubic_formula_c_correct (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] 
                                         [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) 
                (int_quantity_ne_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) ≠ myfld.zero) : 
    cubic_subst f a b c d (cubic_formula_c f a b c d a_ne_zero int_quantity_ne_zero) = myfld.zero := 
begin 
  rw divide_cubic_through f a b c d _ a_ne_zero, 
  have tmp : (cubic_formula_c f a b c d a_ne_zero int_quantity_ne_zero)
              = (((cubic_formula_c f a b c d a_ne_zero int_quantity_ne_zero) .+ ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f)))), 
    simp,
  rw reduce_cubic_to_depressed f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (cubic_formula_c f a b c d a_ne_zero int_quantity_ne_zero) ((cubic_formula_c f a b c d a_ne_zero int_quantity_ne_zero) .+ ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))) tmp, 
  clear tmp, unfold cubic_formula_c, unfold cardano_formula_c, 
  rw <- myfld.add_assoc (cardano_formula f _ _ _ _ _ _) (.- _) _, 
  rw myfld.add_comm (.- _) _, rw myfld.add_negate _, rw zero_simp f _, 
  exact cardano_works f _ _ _ _ _ _, 
end 

lemma int_quantity_eq_zero_simp (f : Type) [myfld f] [fld_not_char_three f] (a1 b c : f) (a_ne_zero : a1 ≠ myfld.zero) : 
  ((three f) .* (a1 .* c)) .+ (.- (square f b)) = myfld.zero -> 
  (((square f (b .* (myfld.reciprocal a1 a_ne_zero))) .* (.- (third f))) .+ (c .* (myfld.reciprocal a1 a_ne_zero))) = myfld.zero := 
begin 
  intros h, 
  unfold square, rw myfld.mul_comm _ (.- _), 
  repeat {rw myfld.mul_assoc _ _ (myfld.reciprocal a1 a_ne_zero) }, 
  rw <- distrib_simp f _ _ _, rw <- mul_zero_by_reciprocal f a1 _ _, 
  rw mul_both_sides f _ _ (three f), rw mul_zero, 
  rw distrib_simp, repeat {rw mul_negate}, rw myfld.mul_comm (_ .* _) (three f), 
  rw myfld.mul_assoc (three f) (third f) _, 
  unfold third, rw myfld.mul_reciprocal (three f) _, rw one_mul_simp, 
  rw mul_both_sides f _ _ a1, rw distrib_simp, rw mul_zero, rw mul_negate, 
  rw myfld.mul_comm _ b, repeat {rw <- myfld.mul_assoc}, 
  rw myfld.mul_comm _ a1, rw myfld.mul_reciprocal a1 _, rw simp_mul_one, 

  unfold square at h, rw myfld.mul_comm c _, rw myfld.mul_assoc at h, rw myfld.add_comm at h, 
  cc, cc, exact fld_not_char_three.not_char_three, 
end 

def cubic_formula_a_alt (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) (int_quantity_eq_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) = myfld.zero) : f 
  := ((depressed_cubic_solution_c_zero_a f (((square f (b .* (myfld.reciprocal a a_ne_zero))) .* (.- (third f))) .+ (c .* (myfld.reciprocal a a_ne_zero))) ((twenty_seventh f) .* ((((two f) .* (cubed f (b .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((nine f) .* ((b .* (myfld.reciprocal a a_ne_zero)) .* (c .* (myfld.reciprocal a a_ne_zero)))))) .+ ((twenty_seven f) .* (d .* (myfld.reciprocal a a_ne_zero))))) (int_quantity_eq_zero_simp f a b c a_ne_zero int_quantity_eq_zero)) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))))

lemma cubic_formula_a_alt_correct (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) (int_quantity_eq_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) = myfld.zero) : 
    cubic_subst f a b c d (cubic_formula_a_alt f a b c d a_ne_zero int_quantity_eq_zero) = myfld.zero := 
begin 
  rw divide_cubic_through f a b c d _ a_ne_zero, 
  have tmp : (cubic_formula_a_alt f a b c d a_ne_zero int_quantity_eq_zero)
              = (((cubic_formula_a_alt f a b c d a_ne_zero int_quantity_eq_zero) .+ ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f)))), 
    simp, 
  rw reduce_cubic_to_depressed f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (cubic_formula_a_alt f a b c d a_ne_zero int_quantity_eq_zero) ((cubic_formula_a_alt f a b c d a_ne_zero int_quantity_eq_zero) .+ ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))) tmp, 
  clear tmp, unfold cubic_formula_a_alt, unfold depressed_cubic_solution_c_zero_a, 
  rw <- myfld.add_assoc (depressed_cubic_solution_c_zero f _ _ _ _ _) (.- _) _, 
  rw myfld.add_comm (.- _) _, rw myfld.add_negate _, rw zero_simp f _, 
  exact depressed_cubic_solution_c_zero_correct f _ _ _ fld_with_cube_root.cubrt (cubrt_cubed f), 
end 

def cubic_formula_b_alt (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) (int_quantity_eq_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) = myfld.zero) : f 
  := ((depressed_cubic_solution_c_zero_b f (((square f (b .* (myfld.reciprocal a a_ne_zero))) .* (.- (third f))) .+ (c .* (myfld.reciprocal a a_ne_zero))) ((twenty_seventh f) .* ((((two f) .* (cubed f (b .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((nine f) .* ((b .* (myfld.reciprocal a a_ne_zero)) .* (c .* (myfld.reciprocal a a_ne_zero)))))) .+ ((twenty_seven f) .* (d .* (myfld.reciprocal a a_ne_zero))))) (int_quantity_eq_zero_simp f a b c a_ne_zero int_quantity_eq_zero)) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))))

def cubic_formula_c_alt (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
  (a b c d : f) (a_ne_zero : a ≠ myfld.zero) (int_quantity_eq_zero : ((three f) .* (a .* c)) .+ (.- (square f b)) = myfld.zero) : f 
  := ((depressed_cubic_solution_c_zero_c f (((square f (b .* (myfld.reciprocal a a_ne_zero))) .* (.- (third f))) .+ (c .* (myfld.reciprocal a a_ne_zero))) ((twenty_seventh f) .* ((((two f) .* (cubed f (b .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((nine f) .* ((b .* (myfld.reciprocal a a_ne_zero)) .* (c .* (myfld.reciprocal a a_ne_zero)))))) .+ ((twenty_seven f) .* (d .* (myfld.reciprocal a a_ne_zero))))) (int_quantity_eq_zero_simp f a b c a_ne_zero int_quantity_eq_zero)) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))))

/- And so, as long as it is decidable whether a quantity is equal to zero or not, 
     we have a viable solution to any cubic.-/ 

/- The next goal is to prove uniqueness of those solutions. As thie is going to involve the cardano formula 
    and the cube roots of unity, we can start with some intermediate lemmae.-/ 

lemma cube_roots_sum_zero (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_with_cube_root f] (x : f) : 
    (fld_with_cube_root.cubrt x) .+ ((alt_cubrt_a f x) .+ (alt_cubrt_b f x)) = myfld.zero := 
begin 
  unfold alt_cubrt_a, unfold alt_cubrt_b, unfold cube_root_of_unity, 
  rw <- distrib_simp f _ _ (fld_with_cube_root.cubrt x), 
  have tmp : (fld_with_cube_root.cubrt x) = myfld.one .* (fld_with_cube_root.cubrt x) , 
    rw myfld.mul_comm, exact myfld.mul_one (fld_with_cube_root.cubrt x), 
  rw [tmp] {occs := occurrences.pos [1]}, clear tmp, 
  rw <- distrib_simp f _ _ (fld_with_cube_root.cubrt x), 
  have h : (myfld.one .+ (( .- myfld.one .+ sqroot .- (three f)) .* (myfld.reciprocal (two f) _) .+ ( .- myfld.one .+ .- sqroot .- (three f)) .* (myfld.reciprocal (two f) _))) = myfld.zero,
  rw myfld.add_comm _ (.- (sqroot _)), 
  rw distrib_simp f _ _ _, rw distrib_simp f _ _ _, repeat {rw mul_negate f _ _}, 
  rw one_mul_simp f _, 
  repeat {rw <- myfld.add_assoc _ _ _}, rw myfld.add_assoc (_ .* _) (.- _) _, 
  rw myfld.add_negate _, rw simp_zero f _, 
  rw <- add_negate f _ _, 
  rw only_one_reciprocal f (two f) _ (two_ne_zero f), 
  rw add_two_halves f, 
  exact myfld.add_negate myfld.one,
  rw h, exact mul_zero f _,
end 

/- Proving uniqueness will involve expalnding the cubic (x - solution_a) (x - solution_b) (x - solution_c) . 
    This is the x^2 term (0) in the resulting cubic.-/ 
lemma cardano_formulae_sum_zero (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] [fld_with_cube_root f] [fld_not_char_three f] 
    (c d : f) (c_ne_zero : c ≠ myfld.zero) : 
  (cardano_formula_a f c d c_ne_zero) .+ ((cardano_formula_b f c d c_ne_zero) .+ (cardano_formula_c f c d c_ne_zero))
      = myfld.zero := 
begin 
  have mul_zero_by_anything : ∀(x y : f), (x = myfld.zero) -> x .* y = myfld.zero,
    intros x y hx, rw hx, rw mul_zero,
  unfold cardano_formula_a, unfold cardano_formula_b, unfold cardano_formula_c, unfold cardano_formula, 
  /- First move all the cube root terms to the start - they must sum to zero by the previous lemma.-/ 
  rw <- myfld.add_assoc (alt_cubrt_a f _) _ _, rw myfld.add_assoc _ (alt_cubrt_b f _) _, 
  rw myfld.add_comm _ (alt_cubrt_b f _), rw <- myfld.add_assoc (alt_cubrt_b f _) _ _, 
  rw myfld.add_assoc (alt_cubrt_a f _) (alt_cubrt_b f _) _, 
  rw myfld.add_assoc (_ .+ _) (_ .+ _) (_ .+ _), 
  rw <- myfld.add_assoc (fld_with_cube_root.cubrt _) (.- _) (_ .+ _), 
  rw myfld.add_comm (.- _) ((alt_cubrt_a f _) .+ (alt_cubrt_b f _)), 
  rw myfld.add_assoc (fld_with_cube_root.cubrt _) (_ .+ _) (.- _), 
  rw cube_roots_sum_zero f _, rw simp_zero f _, 

  /- The three remaining terms are all -c/3x, where x is one of the three cube roots. 
     We can first use distributivity to make this into the sum of the reciprocals of the cube roots.-/ 
  rw <- add_negate f _ _, rw <- add_negate f _ _,
  apply negate_zero_a f _, 
  rw <- distrib_simp_alt f c _ _, rw <- distrib_simp_alt f c _ _, 
  rw myfld.mul_comm c _, apply mul_zero_by_anything _ c,
  repeat {rw <- mul_two_reciprocals f _ (three f) _ _}, 
  rw only_one_reciprocal f (three f) _ fld_not_char_three.not_char_three, 
  rw <- distrib_simp f _ _ (myfld.reciprocal (three f) fld_not_char_three.not_char_three), 
  rw <- distrib_simp f _ _ (myfld.reciprocal (three f) fld_not_char_three.not_char_three), 
  apply mul_zero_by_anything _ (myfld.reciprocal (three f) fld_not_char_three.not_char_three), 
  unfold alt_cubrt_a, unfold alt_cubrt_b, 
  rw split_reciprocal f _ (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))), 
  rw split_reciprocal f _ (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))), 
  rw only_one_reciprocal f _ _ (cubrt_nonzero f _ (cardano_den_not_zero_int f c d c_ne_zero)), 
  rw <- distrib_simp f _ _ _, 
  have tmp : (myfld.reciprocal (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) _) = 
            myfld.one .* (myfld.reciprocal (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) _) , 
    rw myfld.mul_comm myfld.one _, exact myfld.mul_one _, 
    exact cubrt_nonzero f _ (cardano_den_not_zero_int f c d c_ne_zero), 
  rw [tmp] {occs := occurrences.pos [1]}, clear tmp, 
  rw only_one_reciprocal f _ _ (cubrt_nonzero f _ (cardano_den_not_zero_int f c d c_ne_zero)), 
  rw <- distrib_simp f _ _ _, 
  apply mul_zero_by_anything _ _, 

  /- And now we just prove that the reciprocals of the cube roots of unity add to zero. -/ 
  unfold cube_root_of_unity, 
  repeat {rw split_reciprocal f _ _ _}, rw double_reciprocal f _ _, rw <- distrib_simp f _ _ (two f), 
  rw add_two_reciprocals f _ _ _ _, 
  rw <- myfld.add_assoc (.- myfld.one) _ (_ .+ _), 
  have tmp : (.- myfld.one) .+ (.- (sqroot (.- (three f)))) = 
             (.- (sqroot (.- (three f)))) .+ (.- myfld.one) , 
    exact myfld.add_comm (.- myfld.one) (.- (sqroot (.- (three f)))), 
  rw [tmp] {occs := occurrences.pos [1]}, clear tmp, 
  rw myfld.add_assoc (sqroot _) (.- (sqroot _)) _, 
  rw myfld.add_negate (sqroot (.- (three f))), rw simp_zero f _, 
  rw <- add_negate f myfld.one myfld.one, 
  rw reciprocal_rewrite f _ _ (difference_of_squares f (.- myfld.one) (sqroot (.- (three f)))) _, 
  have simp_den : ((square f (.- myfld.one)) .+ (.- (square f (sqroot (.- (three f))))))
                  = (two f) .* (two f) , 
    unfold square, rw mul_negate f _ _, rw <- mul_negate_alt f _ _, rw double_negative f _, rw simp_mul_one f _, 
    rw fld_with_sqrt.sqrt_mul_sqrt _, rw double_negative f _, 
    unfold three, unfold two, simp, 
  rw reciprocal_rewrite f _ ((two f) .* (two f)) simp_den _, 
  rw <- myfld.mul_assoc _ _ _, rw split_reciprocal f (two f) (two f) _, 
  rw <- myfld.mul_assoc (myfld.reciprocal (two f) _) (myfld.reciprocal (two f) _) (two f), 
  rw myfld.mul_comm (myfld.reciprocal (two f) _) (two f), 
  rw myfld.mul_reciprocal (two f) _, rw simp_mul_one f _, 
  rw mul_negate f _ _, unfold two, 
  rw myfld.mul_reciprocal (myfld.one .+ myfld.one) _, 
  exact myfld.add_negate myfld.one, 

  /- And now we just do some of the leftover detritus from the "applies" earlier.-/ 
  apply alt_cubrt_b_nonzero f _, exact cardano_den_not_zero_int f c d c_ne_zero, 
  exact fld_not_char_three.not_char_three, 
  apply alt_cubrt_a_nonzero f _, exact cardano_den_not_zero_int f c d c_ne_zero, 
end 

lemma cardano_products (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d x : f) (c_ne_zero : c ≠ myfld.zero) : 
    ((((cardano_formula_a f c d c_ne_zero) .* (cardano_formula_b f c d c_ne_zero)) .+ ((cardano_formula_a f c d c_ne_zero) .* (cardano_formula_c f c d c_ne_zero))) .+ ((cardano_formula_b f c d c_ne_zero) .* (cardano_formula_c f c d c_ne_zero))) = c := 
begin 

  /- I'm so sorry about this line. 
      What it does is simplify the proof by reducing it to solving the same goal where 
      some of the more complex recurring expressions have been folded down. 
      However, the only nice way to do that is with mathlib, and there are reasons why I *really* 
      didn't want to use that.-/ 
  have folded_version : ∀ (cubrt root_unity_a root_unity_b : f), 
                      ∀ (cubrt_ne_zero : cubrt ≠ myfld.zero), 
                      ∀ (root_unity_a_ne_zero : root_unity_a ≠ myfld.zero), 
                      ∀ (root_unity_b_ne_zero : root_unity_b ≠ myfld.zero), (cubrt = (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) -> root_unity_a = (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f)))) -> root_unity_b = (cube_root_of_unity f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f)))) -> (((cubrt .+ (.- (c .* (myfld.reciprocal (cubrt .* (three f)) (mul_nonzero f cubrt (three f) cubrt_ne_zero fld_not_char_three.not_char_three))))) .* ((root_unity_a .* cubrt) .+ (.- (c .* (myfld.reciprocal ((root_unity_a .* cubrt) .* (three f)) (mul_nonzero f (root_unity_a .* cubrt) (three f) (mul_nonzero f root_unity_a cubrt root_unity_a_ne_zero cubrt_ne_zero) fld_not_char_three.not_char_three)))))) .+ ((cubrt .+ (.- (c .* (myfld.reciprocal (cubrt .* (three f)) (mul_nonzero f cubrt (three f) cubrt_ne_zero fld_not_char_three.not_char_three))))) .* ((root_unity_b .* cubrt) .+ (.- (c .* (myfld.reciprocal ((root_unity_b .* cubrt) .* (three f)) (mul_nonzero f (root_unity_b .* cubrt) (three f) (mul_nonzero f root_unity_b cubrt root_unity_b_ne_zero cubrt_ne_zero) fld_not_char_three.not_char_three))))))) .+ (((root_unity_a .* cubrt) .+ (.- (c .* (myfld.reciprocal ((root_unity_a .* cubrt) .* (three f)) (mul_nonzero f (root_unity_a .* cubrt) (three f) (mul_nonzero f root_unity_a cubrt root_unity_a_ne_zero cubrt_ne_zero) fld_not_char_three.not_char_three))))) .* ((root_unity_b .* cubrt) .+ (.- (c .* (myfld.reciprocal ((root_unity_b .* cubrt) .* (three f)) (mul_nonzero f (root_unity_b .* cubrt) (three f) (mul_nonzero f root_unity_b cubrt root_unity_b_ne_zero cubrt_ne_zero) fld_not_char_three.not_char_three)))))) = c), 
    intros cubrt root_unity_a root_unity_b 
       cubrt_n_zero rta_n_zero rtb_n_zero 
       cubrt_h root_unity_a_h root_unity_b_h, 

    /- OK, so that hideous line means that the proof in the sidebar looks much less hideous, but 
          we can still use it to solve the main proof once we finish.-/ 
    /- First take a moment to restate some of the properties of roots.-/ 
    have sum_roots_zero : myfld.one .+ (root_unity_a .+ root_unity_b) = myfld.zero, 
      rw root_unity_a_h, rw root_unity_b_h, 
      have tmp : myfld.one .+ ((cubrt_unity_a f) .+ (cubrt_unity_b f)) = myfld.zero, 
        exact cubrts_unity_sum_zero f, 
      unfold cubrt_unity_a at tmp, unfold cubrt_unity_b at tmp, unfold cube_root_of_unity, exact tmp, 

    have product_roots_one : root_unity_a .* root_unity_b = myfld.one, 
      rw root_unity_a_h, rw root_unity_b_h, unfold cube_root_of_unity, 
      rw <- myfld.mul_assoc _ (myfld.reciprocal (two f) _) _, rw myfld.mul_comm (myfld.reciprocal (two f) _) _, 
      rw <- myfld.mul_assoc _ (myfld.reciprocal (two f) _) (myfld.reciprocal (two f) _), 
      rw mul_two_reciprocals f (two f) (two f) _ _, 
      rw myfld.mul_assoc _ _ (myfld.reciprocal _ _), 
      rw difference_of_squares f (.- (myfld.one)) _, 
      rw sqrt_squared f _, unfold square, rw mul_negate f _ _, rw mul_negate_alt_simp f _ _, 
      repeat {rw double_negative f _}, rw one_mul_simp f _, 
      unfold two, unfold three, simp, 

    have root_a_reciprocal : ∀ (rta_prf : root_unity_a ≠ myfld.zero), 
                              myfld.reciprocal root_unity_a rta_prf = root_unity_b, 
      intros prf, symmetry, exact only_one_reciprocal_alt f root_unity_a root_unity_b _ product_roots_one, 
    have root_b_reciprocal : ∀ (rtb_prf : root_unity_b ≠ myfld.zero), 
                              myfld.reciprocal root_unity_b rtb_prf = root_unity_a, 
      intros prf, symmetry, rw myfld.mul_comm at product_roots_one, 
          exact only_one_reciprocal_alt f root_unity_b root_unity_a _ product_roots_one, 
    have sum_alt_roots_minusone : root_unity_a .+ root_unity_b = .- myfld.one, 
      have tmp : (myfld.one .+ (root_unity_a .+ root_unity_b)) .+ (.- myfld.one) = .- myfld.one, 
        rw sum_roots_zero, rw simp_zero f _, 
      rw <- myfld.add_assoc myfld.one (_ .+ _) (.- _) at tmp, rw myfld.add_comm (_ .+ _) (.- myfld.one) at tmp, 
      rw myfld.add_assoc myfld.one (.- myfld.one) _ at tmp, rw myfld.add_negate myfld.one at tmp, rw simp_zero f _ at tmp, exact tmp, 
    have root_a_squ : root_unity_a .* root_unity_a = root_unity_b, 
      have tmp : root_unity_a .+ (myfld.reciprocal root_unity_a rta_n_zero) = .- (myfld.one), 
        rw root_a_reciprocal rta_n_zero, exact sum_alt_roots_minusone, 
      have tmp2 : (root_unity_a .+ (myfld.reciprocal root_unity_a rta_n_zero)) .* root_unity_a = .- root_unity_a, 
        rw tmp, rw mul_negate f _ _, rw one_mul_simp f root_unity_a, clear tmp, 
      rw distrib_simp f _ _ _ at tmp2, 
      rw carry_term_across f (root_unity_a .* root_unity_a) (.- root_unity_a) ((myfld.reciprocal root_unity_a rta_n_zero) .* root_unity_a) at tmp2, 
      rw myfld.mul_comm (myfld.reciprocal _ _) root_unity_a at tmp2, rw myfld.mul_reciprocal root_unity_a _ at tmp2, 
      rw myfld.add_assoc at sum_roots_zero, rw myfld.add_comm (_ .+ _) root_unity_b at sum_roots_zero, 
      rw carry_term_across f _ _ _ at sum_roots_zero, 
      rw <- add_negate _ _ at tmp2, rw simp_zero _ at sum_roots_zero, 
      rw myfld.add_comm root_unity_a myfld.one at tmp2, rw <- sum_roots_zero at tmp2, exact tmp2, 
    have root_b_squ : root_unity_b .* root_unity_b = root_unity_a, 
      rw <- root_a_squ, rw [root_a_squ] {occs := occurrences.pos [2]}, 
      rw <- myfld.mul_assoc, rw product_roots_one, rw <- myfld.mul_one root_unity_a, 

    /-have a_squared_b : root_unity_a .* root_unity_a = root_unity_b, 
      rw root_unity_a_h, rw root_unity_b_h, -/ 

    /- Start by multiplying out all the brackets and cancelling in terms with cubrt * reciprocal (cubrt) .-/ 
    repeat {rw distrib_simp f _ _ _}, repeat {rw distrib_simp_alt f _ _ _}, 
    repeat {rw mul_negate f _ _}, repeat {rw mul_negate_alt_simp f _ _}, repeat {rw double_negative f _}, 
    have tmp : ∀ (x : f), ((x .* cubrt) .* (three f)) = cubrt .* (x .* (three f)) , 
      intro x, simp, 
    rw reciprocal_rewrite f _ _ (tmp root_unity_a) _, rw reciprocal_rewrite f _ _ (tmp root_unity_b) _, 
    /- Some sensible-looking stuff now doesn't work because it's rewriting inside the proofs that are keeping the reciprocals legal. -/ 
    /- To make it work we're gonna need to do a massive only_one_reciprocal.-/ 
    rw only_one_reciprocal f (cubrt .* (root_unity_a .* (three f))) _ (mul_nonzero f cubrt (root_unity_a .* (three f)) cubrt_n_zero (mul_nonzero f root_unity_a (three f) rta_n_zero fld_not_char_three.not_char_three)), 
    rw only_one_reciprocal f (cubrt .* (root_unity_b .* (three f))) _ (mul_nonzero f cubrt (root_unity_b .* (three f)) cubrt_n_zero (mul_nonzero f root_unity_b (three f) rtb_n_zero fld_not_char_three.not_char_three)), 
    repeat {rw myfld.mul_comm _ cubrt}, 
    repeat {rw myfld.mul_assoc cubrt c (myfld.reciprocal _ _) }, repeat {rw myfld.mul_comm cubrt c}, 
    repeat {rw <- myfld.mul_assoc c cubrt (myfld.reciprocal _ _) }, 
    repeat {rw cancel_from_reciprocal_alt f cubrt _ _}, 
    repeat {rw myfld.mul_assoc (c .* _) cubrt _}, repeat {rw <- myfld.mul_assoc c (myfld.reciprocal _ _) cubrt}, 
    repeat {rw cancel_from_reciprocal f cubrt _ _}, 

    /- Now we gather all of the (cubrt^2) terms together, and they cancel out as there is one for each 
         of the cube roots of unity.-/ 
    rw myfld.mul_assoc (cubrt .* root_unity_a) cubrt root_unity_b, 
    rw myfld.mul_comm (cubrt .* root_unity_a) cubrt, 
    repeat {rw myfld.mul_assoc cubrt cubrt _}, repeat {rw <- myfld.mul_assoc (cubrt .* cubrt) _ _}, 
    repeat {rw <- myfld.add_assoc ((cubrt .* cubrt) .* _) _ _}, 
    repeat {rw myfld.add_assoc _ ((cubrt .* cubrt) .* _) _}, 
    repeat {rw myfld.add_comm _ ((cubrt .* cubrt) .* _) }, 
    repeat {rw <- myfld.add_assoc ((cubrt .* cubrt) .* _) _ _}, 
    rw myfld.add_assoc ((cubrt .* cubrt) .* _) ((cubrt .* cubrt) .* _) _, 
    rw <- distrib_simp_alt f (cubrt .* cubrt) _ _, 
    rw myfld.add_assoc ((cubrt .* cubrt) .* _) ((cubrt .* cubrt) .* _) _, 
    rw <- distrib_simp_alt f (cubrt .* cubrt) _ _, 
    rw product_roots_one, 
    rw myfld.add_comm root_unity_a myfld.one, rw <- myfld.add_assoc myfld.one root_unity_a root_unity_b, 
    rw sum_roots_zero, rw zero_mul f _, rw simp_zero f _, 

    /- Now we can do the same with the terms containing a factor of c^2/cubrt^2-/ 
    have tmp2 : ∀ (x y : f), (c .* x) .* (c .* y) = (c .* c) .* (x .* y) , 
      intros x y, 
      rw myfld.mul_assoc (c .* x) c y, rw <- myfld.mul_assoc c x c, rw myfld.mul_comm x c, 
      rw myfld.mul_assoc _ _ _, rw myfld.mul_assoc _ _ _, 
    repeat {rw tmp2 _ _}, clear tmp2, clear tmp, 
    repeat {rw mul_two_reciprocals f _ _ _ _}, 
      /- We now have some convoluted reciprocals that need to be simplified. This needs to be done 
           in sub-proofs so that it can be done in a single step with reciprocal_rewrite.-/ 
    have reciprocal_1 : ((cubrt .* (three f)) .* (cubrt .* (root_unity_a .* (three f)))) = 
                (square f (cubrt .* (three f))) .* root_unity_a,
      unfold square, simp, 
    rw reciprocal_rewrite f _ _ reciprocal_1 _, 
    have reciprocal_2 : ((cubrt .* (three f)) .* (cubrt .* (root_unity_b .* (three f)))) = 
                (square f (cubrt .* (three f))) .* root_unity_b,
      unfold square, simp, 
    rw reciprocal_rewrite f _ _ reciprocal_2 _, 
    have reciprocal_3 : ((cubrt .* (root_unity_a .* (three f))) .* (cubrt .* (root_unity_b .* (three f)))) = 
    (square f (cubrt .* (three f))) .* (root_unity_a .* root_unity_b) , 
      unfold square, exact mul_complex f _ _ _ _, 
    rw product_roots_one at reciprocal_3, rw reciprocal_rewrite f _ _ reciprocal_3 _, 
    repeat {rw split_reciprocal f (square f (cubrt .* (three f))) _ _}, 
    repeat {rw myfld.mul_assoc (c .* c) (myfld.reciprocal (square f _) _) (myfld.reciprocal _ _) }, 

    repeat {rw myfld.add_comm _ (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) }, 
    repeat {rw myfld.add_assoc _ (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) _}, 
    repeat {rw myfld.add_comm _ (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) }, 
    repeat {rw <- myfld.add_assoc (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) _ _}, 
    repeat {rw myfld.add_assoc _ (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) _}, 
    repeat {rw myfld.add_comm _ (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) }, 
    rw <- myfld.add_assoc (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) _ _, 
    rw myfld.add_assoc (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) _, 
    rw <- distrib_simp_alt f ((c .* c) .* (myfld.reciprocal _ _)) _ _, 
    repeat {rw <- myfld.add_assoc (((c .* c) .* (myfld.reciprocal _ _)) .* (myfld.reciprocal _ _)) _ _}, 
    rw myfld.add_assoc (((c .* c) .* (myfld.reciprocal _ _)) .* _) (((c .* c) .* (myfld.reciprocal _ _)) .* _) _, 
    rw <- distrib_simp_alt f ((c .* c) .* (myfld.reciprocal _ _)) _ _, 
    rw root_a_reciprocal _, rw root_b_reciprocal _, rw recip_one_one f _, 
    rw myfld.add_comm root_unity_b myfld.one, rw <- myfld.add_assoc myfld.one root_unity_b root_unity_a, 
    rw myfld.add_comm root_unity_b root_unity_a, 
    rw sum_roots_zero, rw zero_mul f _, rw simp_zero f _, 
    clear reciprocal_1, clear reciprocal_2, clear reciprocal_3, 

    /- Some minor cancellation that should maybe have been done earlier but wasn't...-/ 
    rw myfld.mul_comm cubrt root_unity_a, repeat {rw <- myfld.mul_assoc root_unity_a cubrt (_ .* _) }, 
    rw myfld.mul_assoc cubrt c (myfld.reciprocal _ _), rw myfld.mul_comm cubrt c, 
    rw <- myfld.mul_assoc c cubrt (myfld.reciprocal _ _), 
    rw cancel_from_reciprocal_alt f cubrt _ _, 
    clear cubrt_h, /- This also lets us get rid of the cubrt variable entirely, which is nice.-/ 
    repeat {rw split_reciprocal f _ _ _}, 
    rw only_one_reciprocal f root_unity_a _ rta_n_zero, 
    rw only_one_reciprocal f root_unity_b _ rtb_n_zero, 
    rw only_one_reciprocal f (three f) _ fld_not_char_three.not_char_three, 
    clear cubrt_n_zero, clear cubrt, 
    repeat {rw <- add_negate f _ _}, repeat {rw root_a_reciprocal _}, repeat {rw root_b_reciprocal _}, 
    clear root_a_reciprocal, clear root_b_reciprocal, clear rta_n_zero, clear rtb_n_zero, 
    clear root_unity_a_h, clear root_unity_b_h, 

    /- Every remainining term is a factor of c/3, so we can pull that out.-/ 
    rw myfld.mul_assoc root_unity_a c (_ .* _), rw myfld.mul_comm root_unity_a c, 
    repeat {rw <- myfld.mul_assoc c _ _}, 
    repeat {rw <- distrib_simp_alt f c _ _}, 
    rw myfld.mul_assoc root_unity_a root_unity_a _, rw root_a_squ, clear root_a_squ, 
    rw myfld.mul_comm (root_unity_b .* _) root_unity_b, rw myfld.mul_assoc root_unity_b root_unity_b _, 
    rw root_b_squ, clear root_b_squ, 
    repeat {rw myfld.mul_comm _ (myfld.reciprocal (three f) _) }, 
    repeat {rw <- distrib_simp_alt f (myfld.reciprocal (three f) _) _ _}, 

    /- And now we have -c * 1/3 * -3, so c.-/ 
    rw myfld.add_comm root_unity_b root_unity_a, rw sum_alt_roots_minusone, 
    repeat {rw <- add_negate f _ _}, rw <- mul_negate_alt f (myfld.reciprocal (three f) _) (_ .+ _), 
    rw <- mul_negate_alt f _ _, rw double_negative f _, 
    rw myfld.mul_comm (myfld.reciprocal _ _) (_ .+ _), 
    unfold three, rw <- myfld.add_assoc myfld.one myfld.one myfld.one, 
    rw myfld.mul_reciprocal (myfld.one .+ (myfld.one .+ myfld.one)) _, 
    symmetry, exact myfld.mul_one c, 

  unfold cardano_formula_a, unfold cardano_formula_b, unfold cardano_formula_c, unfold cardano_formula, 
  unfold alt_cubrt_a, unfold alt_cubrt_b, 
  have tmp1 : (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) = (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))), refl, 
  have tmp2 : (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f)))) = (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f)))), refl, 
  have tmp3 : (cube_root_of_unity f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f)))) = (cube_root_of_unity f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f)))), refl, 
  exact folded_version 
    (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)))
    (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f))))
    (cube_root_of_unity f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f))))
    (cubrt_nonzero f ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) (cardano_den_not_zero_int f c d c_ne_zero))
    (cubrt_unity_nonzero f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f))))
    (cubrt_unity_nonzero f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f))))
    tmp1 tmp2 tmp3, 
  /- You tried to do this bit with mathlib, which would have made it prettier. 
      However, the display bugs and over-aggressive rewriter made it impractical.-/ 
  /-set cubrt := (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))), 
  set root_unity_a := (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f)))) with rt_unity_a_h, 
  repeat {rw split_reciprocal f _ _ _}, 
  have tmp : (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f))))
                = root_unity_a, 
    rw rt_unity_a_h, 
  rw reciprocal_rewrite f (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f)))) root_unity_a tmp _, 
  rw reciprocal_rewrite f (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f)))) root_unity_a tmp _, -/ 
end 

/- This is used to end the next proof, because that's long enough that it's starting to lag visual studio, 
     so moving part of it out to somewhere else seems smart.-/ 
lemma cardano_product_helper (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
    (c d : f) (c_ne_zero : c ≠ myfld.zero) : (((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) .+ (.- ((((myfld.reciprocal ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) (cardano_den_not_zero_int f c d c_ne_zero)) .* (myfld.reciprocal ((three f) .* ((three f) .* (three f))) (mul_nonzero f (three f) ((three f) .* (three f)) fld_not_char_three.not_char_three (mul_nonzero f (three f) (three f) fld_not_char_three.not_char_three fld_not_char_three.not_char_three)))) .* (c .* c)) .* c)))
  = .- d := 
begin 
  /- Start by rationalising the denominator.-/ 
  have tmp_rat_den : (myfld.reciprocal ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) (cardano_den_not_zero_int f c d c_ne_zero))
                    = 
                    ((myfld.reciprocal ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) (cardano_den_not_zero_int f c d c_ne_zero)) .* ((myfld.reciprocal ((cardano_intermediate_val f c d) .+ (.- (cardano_other_int_val f d))) (cardano_den_not_zero_int_alt f c d c_ne_zero)) .* ((cardano_intermediate_val f c d) .+ (.- (cardano_other_int_val f d))))), 
    rw myfld.mul_comm (myfld.reciprocal _ _) (_ .+ _), rw myfld.mul_reciprocal _ _, rw simp_mul_one f _, 
  rw tmp_rat_den, clear tmp_rat_den, 
  rw myfld.mul_assoc (myfld.reciprocal _ _) (myfld.reciprocal _ _) _, 
  rw mul_two_reciprocals f _ _ _ _, 
  rw reciprocal_rewrite f _ _ (difference_of_squares f _ _) _, 

  /- Now we can simplify the denominator.-/ 
  rw myfld.mul_comm _ (myfld.reciprocal (_ .* _) _), 
  rw myfld.mul_assoc (myfld.reciprocal _ _) (myfld.reciprocal _ _) _, 
  rw mul_two_reciprocals f _ _ _ _, 
  have denom_simp : (((three f) .* ((three f) .* (three f))) .* ((square f (cardano_intermediate_val f c d)) .+ (.- (square f (cardano_other_int_val f d)))))
                      = c .* (c .* c) , 
    unfold cardano_intermediate_val, unfold cardano_other_int_val, 
    rw sqrt_squared f _, unfold square, 
    repeat {rw mul_negate_alt_simp f _ _}, rw double_negative f _, 
    rw [ (myfld.mul_comm d (myfld.reciprocal _ _)) ] {occs := occurrences.pos [2]}, 
    rw mul_negate f _ _, rw myfld.mul_assoc (d .* _) _ d, 
    rw <- myfld.mul_assoc d (myfld.reciprocal _ _) (myfld.reciprocal _ _), 
    rw mul_two_reciprocals f (two f) (two f) _ _, 
    rw myfld.mul_comm (_ .* _) d, rw myfld.mul_assoc d d _, 
    rw myfld.add_comm _ (.- (_ .* _)), 
    rw myfld.add_assoc (.- _) (_ .* _), 
    unfold four, rw myfld.add_comm (.- _) _, 
    rw reciprocal_rewrite f _ _ (two_plus_two f) _, 
    rw only_one_reciprocal f ((two f) .* (two f)) _ (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two), 
    rw myfld.add_negate _, rw simp_zero f _, 
    rw myfld.mul_assoc ((three f) .* _) (cubed f c) _, rw myfld.mul_comm _ (cubed f c), 
    unfold twenty_seven, unfold nine, 
    rw <- myfld.mul_assoc (cubed f c) ((three f) .* _) (myfld.reciprocal _ _), 
    rw myfld.mul_reciprocal _ _, unfold cubed, simp, 
  rw reciprocal_rewrite f _ _ denom_simp _, 

  /- The c^3 on the numerator now cancels with the denominator.-/ 
  repeat {rw <- myfld.mul_assoc}, rw myfld.mul_comm _ ((c .* c) .* c), 
  rw myfld.mul_assoc (myfld.reciprocal _ _) ((c .* c) .* c) _, 
  rw <- myfld.mul_assoc c c c, rw myfld.mul_comm (myfld.reciprocal _ _) (c .* (c .* c)), 
  rw myfld.mul_reciprocal (c .* (c .* c)) _, rw one_mul_simp f _, clear denom_simp, 

  /- The positive intermediate_val cancels with the negative...-/ 
  rw add_negate f _ _, rw double_negative f _, 
  rw myfld.add_assoc (_ .+ _) (.- _) _, 
  rw <- myfld.add_assoc _ _ (.- _), rw myfld.add_comm _ (.- _), 
  rw myfld.add_assoc _ (.- _) _, 
  rw myfld.add_negate _, rw simp_zero f _, 

  /- And ifnally we have to copies of other_int_value added to each other. 
     Each of these is just -d/2, so they add to -d.-/ 
  unfold cardano_other_int_val, 
  rw <- add_negate f _ _, rw <- distrib_simp_alt f d _ _, 
  rw only_one_reciprocal f (two f) _ (two_ne_zero f), 
  rw add_two_halves f, 
  rw simp_mul_one f _, 
end 

lemma cardano_product (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
    (c d : f) (c_ne_zero : c ≠ myfld.zero) : 
    ((cardano_formula_a f c d c_ne_zero) .* ((cardano_formula_b f c d c_ne_zero) .* (cardano_formula_c f c d c_ne_zero)))
       = .- (d) := 
begin 
  /- Again, this line is hideous but actually makes the proof easier to follow in the long run.-/ 
  have folded_version : ∀ (cubrt root_unity_a root_unity_b : f), 
                      ∀ (cubrt_ne_zero : cubrt ≠ myfld.zero), 
                      ∀ (root_unity_a_ne_zero : root_unity_a ≠ myfld.zero), 
                      ∀ (root_unity_b_ne_zero : root_unity_b ≠ myfld.zero), (cubrt = (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) -> root_unity_a = (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f)))) -> root_unity_b = (cube_root_of_unity f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f)))) -> (cubrt .+ (.- (c .* (myfld.reciprocal (cubrt .* (three f)) (mul_nonzero f cubrt (three f) cubrt_ne_zero fld_not_char_three.not_char_three))))) .* (((root_unity_a .* cubrt) .+ (.- (c .* (myfld.reciprocal ((root_unity_a .* cubrt) .* (three f)) (mul_nonzero f (root_unity_a .* cubrt) (three f) (mul_nonzero f root_unity_a cubrt root_unity_a_ne_zero cubrt_ne_zero) fld_not_char_three.not_char_three))))) .* ((root_unity_b .* cubrt) .+ (.- (c .* (myfld.reciprocal ((root_unity_b .* cubrt) .* (three f)) (mul_nonzero f (root_unity_b .* cubrt) (three f) (mul_nonzero f root_unity_b cubrt root_unity_b_ne_zero cubrt_ne_zero) fld_not_char_three.not_char_three)))))) = (.- d)), 


    intros cubrt root_unity_a root_unity_b cubrt_ne_zero rta_n_zero rtb_n_zero 
       cubrt_h root_unity_a_h root_unity_b_h, 

/- TODO: Move all of this crap to somewhere where both sub-proofs can refer to it rather than having 
             all this duplication.-/ 
    have product_roots_one : root_unity_a .* root_unity_b = myfld.one, 
      rw root_unity_a_h, rw root_unity_b_h, unfold cube_root_of_unity, 
      rw <- myfld.mul_assoc _ (myfld.reciprocal (two f) _) _, rw myfld.mul_comm (myfld.reciprocal (two f) _) _, 
      rw <- myfld.mul_assoc _ (myfld.reciprocal (two f) _) (myfld.reciprocal (two f) _), 
      rw mul_two_reciprocals f (two f) (two f) _ _, 
      rw myfld.mul_assoc _ _ (myfld.reciprocal _ _), 
      rw difference_of_squares f (.- (myfld.one)) _, 
      rw sqrt_squared f _, unfold square, rw mul_negate f _ _, rw mul_negate_alt_simp f _ _, 
      repeat {rw double_negative f _}, rw one_mul_simp f _, 
      unfold two, unfold three, simp, 
    have sum_roots_zero : myfld.one .+ (root_unity_a .+ root_unity_b) = myfld.zero, 
      rw root_unity_a_h, rw root_unity_b_h, 
      have tmp : myfld.one .+ ((cubrt_unity_a f) .+ (cubrt_unity_b f)) = myfld.zero, 
        exact cubrts_unity_sum_zero f, 
      unfold cubrt_unity_a at tmp, unfold cubrt_unity_b at tmp, unfold cube_root_of_unity, exact tmp, 
     have root_a_reciprocal : ∀ (rta_prf : root_unity_a ≠ myfld.zero), 
                              myfld.reciprocal root_unity_a rta_prf = root_unity_b, 
      intros prf, symmetry, exact only_one_reciprocal_alt f root_unity_a root_unity_b _ product_roots_one, 
     have root_b_reciprocal : ∀ (rtb_prf : root_unity_b ≠ myfld.zero), 
                              myfld.reciprocal root_unity_b rtb_prf = root_unity_a, 
      intros prf, symmetry, rw myfld.mul_comm at product_roots_one, 
          exact only_one_reciprocal_alt f root_unity_b root_unity_a _ product_roots_one, 
     have sum_alt_roots_minusone : root_unity_a .+ root_unity_b = .- myfld.one, 
      have tmp : (myfld.one .+ (root_unity_a .+ root_unity_b)) .+ (.- myfld.one) = .- myfld.one, 
        rw sum_roots_zero, rw simp_zero f _, 
      rw <- myfld.add_assoc myfld.one (_ .+ _) (.- _) at tmp, rw myfld.add_comm (_ .+ _) (.- myfld.one) at tmp, 
      rw myfld.add_assoc myfld.one (.- myfld.one) _ at tmp, rw myfld.add_negate myfld.one at tmp, rw simp_zero f _ at tmp, exact tmp, 
    have root_a_squ : root_unity_a .* root_unity_a = root_unity_b, 
      have tmp : root_unity_a .+ (myfld.reciprocal root_unity_a rta_n_zero) = .- (myfld.one), 
        rw root_a_reciprocal rta_n_zero, exact sum_alt_roots_minusone, 
      have tmp2 : (root_unity_a .+ (myfld.reciprocal root_unity_a rta_n_zero)) .* root_unity_a = .- root_unity_a, 
        rw tmp, rw mul_negate f _ _, rw one_mul_simp f root_unity_a, clear tmp, 
      rw distrib_simp f _ _ _ at tmp2, 
      rw carry_term_across f (root_unity_a .* root_unity_a) (.- root_unity_a) ((myfld.reciprocal root_unity_a rta_n_zero) .* root_unity_a) at tmp2, 
      rw myfld.mul_comm (myfld.reciprocal _ _) root_unity_a at tmp2, rw myfld.mul_reciprocal root_unity_a _ at tmp2, 
      rw myfld.add_assoc at sum_roots_zero, rw myfld.add_comm (_ .+ _) root_unity_b at sum_roots_zero, 
      rw carry_term_across f _ _ _ at sum_roots_zero, 
      rw <- add_negate _ _ at tmp2, rw simp_zero _ at sum_roots_zero, 
      rw myfld.add_comm root_unity_a myfld.one at tmp2, rw <- sum_roots_zero at tmp2, exact tmp2, 
    have root_b_squ : root_unity_b .* root_unity_b = root_unity_a, 
      rw <- root_a_squ, rw [root_a_squ] {occs := occurrences.pos [2]}, 
      rw <- myfld.mul_assoc, rw product_roots_one, rw <- myfld.mul_one root_unity_a, 

    repeat {rw distrib_simp f _ _ _}, repeat {rw distrib_simp_alt f _ _ _}, 

    /- First cancel cubrt and 1/cubrt in some terms.-/ 
    repeat {rw mul_negate f _ _}, repeat {rw mul_negate_alt_simp f _ _}, repeat {rw double_negative f _}, 
    repeat {rw myfld.mul_comm c (myfld.reciprocal _ _) }, 
    repeat {rw <- myfld.mul_assoc (myfld.reciprocal _ _) c _}, repeat {rw myfld.mul_assoc cubrt (myfld.reciprocal _ _) _}, 
    rw myfld.mul_assoc (_ .* cubrt) (myfld.reciprocal _ _) _, 
    rw <- myfld.mul_assoc _ cubrt (myfld.reciprocal _ _), 
    have tmp : ∀ (rt : f), ((rt .* cubrt) .* (three f)) = cubrt .* (rt .* (three f)) , 
      simp, 
    repeat {rw reciprocal_rewrite f _ _ (tmp _) _}, 
    repeat {rw cancel_from_reciprocal_alt f cubrt _ _}, 
    /- Some of this bit is slightly more convoluted than you'd expect so as to avoid making the 
        result type-incorrect by rewriting in a reciprocal as collateral damage.-/ 
    rw myfld.mul_assoc c (root_unity_a .* cubrt) (root_unity_b .* cubrt), 
    rw myfld.mul_assoc c root_unity_a cubrt, rw myfld.mul_comm (c .* root_unity_a) cubrt, 
    rw <- myfld.mul_assoc cubrt (c .* root_unity_a) _, 
    rw myfld.mul_assoc (myfld.reciprocal _ _) cubrt _, 
    rw myfld.mul_assoc c root_unity_b cubrt, rw myfld.mul_comm (c .* root_unity_b) cubrt, 
    repeat {rw myfld.mul_assoc (myfld.reciprocal _ _) cubrt _}, 
    repeat {rw cancel_from_reciprocal f cubrt _ _}, 

    /- We can now collect like terms together, as three terms have a factor of cubrt 
        and three terms have a factor of 1/cubrt.-/ 
    repeat {rw myfld.mul_comm (myfld.reciprocal _ _) cubrt}, 
    rw <- myfld.add_assoc (.- _) _ _, rw myfld.add_assoc _ (.- _) _, 
    repeat {rw myfld.add_comm _ (.- _) }, 
    rw <- myfld.add_assoc (.- _) _ _, rw myfld.add_assoc _ (.- _) _, 
    repeat {rw myfld.add_comm _ (.- _) }, 
    rw myfld.add_assoc (.- _) (.- _) _, rw <- add_negate f _ _, 
    repeat {rw <- myfld.add_assoc (.- _) _ _}, 
    rw myfld.add_assoc (.- _) (.- _) _, rw <- add_negate f _ _, 
    rw myfld.mul_assoc (c .* root_unity_a) root_unity_b cubrt, 
    rw myfld.mul_assoc (myfld.reciprocal (three f) _) (_ .* _) cubrt, 
    rw myfld.mul_comm (_ .* _) cubrt, 
    rw <- myfld.mul_assoc cubrt _ _, 
    rw <- distrib_simp_alt f cubrt _ _, rw <- distrib_simp_alt f cubrt _ _, 
    /- cubrt term done, now 1/cubrt term-/ 
    have tmp2 : (cubrt .* (root_unity_b .* (three f))) = 
                ((cubrt .* (three f)) .* root_unity_b), simp, 
    rw reciprocal_rewrite f _ _ tmp2 _, 
    rw split_reciprocal f (cubrt .* (three f)) _ _, 
    rw <- myfld.mul_assoc (myfld.reciprocal (cubrt .* (three f)) _) _ _, 
    rw myfld.mul_assoc _ (myfld.reciprocal (cubrt .* (three f)) _) _, 
    rw myfld.mul_comm _ (myfld.reciprocal (cubrt .* (three f)) _), 
    rw <- myfld.mul_assoc (myfld.reciprocal (cubrt .* (three f)) _) _ _, 
    rw myfld.mul_assoc _ (myfld.reciprocal (cubrt .* (three f)) _) _, 
    rw myfld.mul_comm _ (myfld.reciprocal (cubrt .* (three f)) _), 
    rw <- myfld.mul_assoc (myfld.reciprocal (cubrt .* (three f)) _) _ _, 
    rw only_one_reciprocal f (cubrt .* (three f)) _ (mul_nonzero f cubrt (three f) cubrt_ne_zero fld_not_char_three.not_char_three), 
    rw myfld.add_comm (.- _) ((myfld.reciprocal (cubrt .* (three f)) _) .* _), 
    rw myfld.add_assoc ((myfld.reciprocal (cubrt .* (three f)) _) .* _) ((myfld.reciprocal (cubrt .* (three f)) _) .* _) (.- _), 
    rw <- distrib_simp_alt f (myfld.reciprocal (cubrt .* (three f)) _) _ _, 
    repeat {rw <- myfld.add_assoc _ _ _}, 
    rw myfld.add_assoc ((myfld.reciprocal (cubrt .* (three f)) _) .* _) ((myfld.reciprocal (cubrt .* (three f)) _) .* _) (.- _), 
    rw <- distrib_simp_alt f (myfld.reciprocal (cubrt .* (three f)) _) _ _, 

    /- The cubrt terms do in fact sum to zero.-/ 
    repeat {rw myfld.mul_comm _ c}, repeat {rw myfld.mul_assoc _ c _}, 
    repeat {rw <- myfld.mul_assoc c _ _}, repeat {rw myfld.mul_assoc _ c _}, 
    repeat {rw myfld.mul_comm (myfld.reciprocal _ _) c}, repeat {rw <- myfld.mul_assoc c _ _}, 
    rw <- distrib_simp_alt f c _ _, rw <- distrib_simp_alt f c _ _, 
    repeat {rw reciprocal_rewrite f (_ .* (three f)) ((three f) .* _) (myfld.mul_comm _ (three f)) }, 
    rw myfld.mul_comm root_unity_a (myfld.reciprocal _ _), 
    rw split_reciprocal f (three f) _ _, rw split_reciprocal f (three f) _ _, 
    repeat {rw <- myfld.mul_assoc (myfld.reciprocal (three f) _) _ _}, 
    rw only_one_reciprocal f (three f) _ fld_not_char_three.not_char_three, 
    rw <- distrib_simp_alt f (myfld.reciprocal (three f) _) _ _, 
    rw <- distrib_simp_alt f (myfld.reciprocal (three f) _) _ _, 
    rw product_roots_one, rw root_a_reciprocal _, rw root_b_reciprocal _, rw root_a_squ, rw root_b_squ, 
    rw sum_roots_zero, repeat {rw zero_mul f _}, rw negate_zero_zero f, rw simp_zero f _, 

    /- And so do the 1/cubrt terms.-/ 
    rw myfld.mul_comm root_unity_b c, rw <- myfld.mul_assoc c root_unity_b root_unity_a, 
    rw myfld.mul_assoc (myfld.reciprocal _ _) c (root_unity_b .* root_unity_a), 
    rw myfld.mul_comm (myfld.reciprocal (three f) _) c, 
    rw <- myfld.mul_assoc c (myfld.reciprocal (three f) _) (root_unity_b .* root_unity_a), 
    repeat {rw myfld.mul_assoc c c _}, repeat {rw myfld.mul_assoc (c .* c) (myfld.reciprocal (three f) _) _}, 
    rw <- distrib_simp_alt f ((c .* c) .* (myfld.reciprocal (three f) _)) _ _, 
    rw <- distrib_simp_alt f ((c .* c) .* (myfld.reciprocal (three f) _)) _ _, 
    rw myfld.mul_comm root_unity_b root_unity_a, rw product_roots_one, 
    rw myfld.add_comm root_unity_b root_unity_a, rw sum_roots_zero, 
    repeat {rw zero_mul f _}, rw simp_zero f _, 

    /- Minor simplifications that should maybe have been done earlier.-/ 
    rw myfld.mul_assoc (root_unity_a .* cubrt) root_unity_b cubrt, 
    rw [ (myfld.mul_comm root_unity_a cubrt) ] {occs := occurrences.pos [1]}, 
    rw <- myfld.mul_assoc cubrt root_unity_a root_unity_b, 
    rw product_roots_one, rw simp_mul_one f _, 
    rw myfld.mul_comm c ((_ .* _) .* _), 
    repeat {rw myfld.mul_assoc _ _ _}, repeat {rw <- myfld.mul_assoc _ _ _}, 
    rw myfld.mul_assoc (myfld.reciprocal _ _) (myfld.reciprocal _ _), 
    rw mul_two_reciprocals f _ _ _ _, 
    rw myfld.mul_assoc (myfld.reciprocal _ _) (myfld.reciprocal _ _), 
    rw mul_two_reciprocals f _ _ _ _, 
    have den_reorder : ((((three f) .* cubrt) .* (cubrt .* (root_unity_a .* (three f)))) .* ((three f) .* cubrt)) = 
                       (((cubrt .* (cubrt .* cubrt)) .* ((three f) .* ((three f) .* (three f)))) .* root_unity_a), 
      rw myfld.mul_comm root_unity_a (three f), rw myfld.mul_assoc cubrt (three f) root_unity_a, repeat {rw myfld.mul_comm (three f) cubrt}, 
      rw <- myfld.mul_assoc (cubrt .* (three f)) _ (cubrt .* (three f)), 
      rw myfld.mul_comm (_ .* root_unity_a) _, 
      repeat {rw <- myfld.mul_assoc cubrt _ _}, repeat {rw myfld.mul_assoc _ cubrt _}, 
      rw myfld.mul_comm (three f) cubrt, 
      repeat {rw <- myfld.mul_assoc cubrt _ _}, repeat {rw myfld.mul_assoc _ cubrt _}, 
      rw myfld.mul_comm (three f) cubrt, 
      repeat {rw myfld.mul_assoc}, 
    rw reciprocal_rewrite f _ _ den_reorder _, 
    rw split_reciprocal f _ root_unity_a _, rw root_a_reciprocal _, 
    repeat {rw <- myfld.mul_assoc}, 
    rw myfld.mul_comm c (root_unity_a .* c), rw myfld.mul_assoc root_unity_b (_ .* _) c, 
    rw myfld.mul_assoc root_unity_b root_unity_a c, 
    rw myfld.mul_comm root_unity_b root_unity_a, rw product_roots_one, rw one_mul f c, 

    /- Now that we only have two fractions left, simplifying the proofs that enable those reciprocals 
    to exist will allow us to throw away all the lemmae about roots, as they are no longer relevant.-/ 
    rw split_reciprocal f (_ .* (_ .* _)) (_ .* (_ .* _)) _, 
    rw only_one_reciprocal f (cubrt .* (cubrt .* cubrt)) _ (mul_nonzero f cubrt (cubrt .* cubrt) cubrt_ne_zero (mul_nonzero f cubrt cubrt cubrt_ne_zero cubrt_ne_zero)), 
    rw only_one_reciprocal f ((three f) .* ((three f) .* (three f))) _ (mul_nonzero f (three f) ((three f) .* (three f)) fld_not_char_three.not_char_three (mul_nonzero f (three f) (three f) fld_not_char_three.not_char_three fld_not_char_three.not_char_three)), 
    clear tmp tmp2 den_reorder root_a_squ root_b_squ sum_alt_roots_minusone root_a_reciprocal root_b_reciprocal sum_roots_zero product_roots_one root_unity_a_h root_unity_b_h rta_n_zero rtb_n_zero root_unity_a root_unity_b, 
    rw myfld.mul_comm c (_ .* _), 

    /- We now have cubrt * (cubrt * cubrt) in some places. As cubrt is a cube root this can be 
        rewritten according to the definition of the cube root.-/ 
    have cubrt_cubed : (cubrt .* (cubrt .* cubrt)) = (cardano_intermediate_val f c d) .+ (cardano_other_int_val f d) , 
      rw myfld.mul_assoc, rw cubrt_h, rw fld_with_cube_root.cubrt_cubed, 
    rw reciprocal_rewrite f _ _ cubrt_cubed _, rw [cubrt_cubed] {occs := occurrences.pos [1]}, 
    rw only_one_reciprocal f _ _ (cardano_den_not_zero_int f c d c_ne_zero), 
    clear cubrt_cubed cubrt_h cubrt_ne_zero cubrt, 

    /- The remaining simplification is outsourced to a separate lemma, as this one is already 
         large enough to lag VS.-/ 
    exact cardano_product_helper f c d c_ne_zero, 

   unfold cardano_formula_a, unfold cardano_formula_b, unfold cardano_formula_c, unfold cardano_formula, 
  unfold alt_cubrt_a, unfold alt_cubrt_b, 
  have tmp1 : (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) = (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))), refl, 
  have tmp2 : (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f)))) = (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f)))), refl, 
  have tmp3 : (cube_root_of_unity f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f)))) = (cube_root_of_unity f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f)))), refl, 
  exact folded_version 
    (fld_with_cube_root.cubrt ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)))
    (cube_root_of_unity f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f))))
    (cube_root_of_unity f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f))))
    (cubrt_nonzero f ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d)) (cardano_den_not_zero_int f c d c_ne_zero))
    (cubrt_unity_nonzero f (sqroot (.- (three f))) (fld_with_sqrt.sqrt_mul_sqrt (.- (three f))))
    (cubrt_unity_nonzero f (.- (sqroot (.- (three f)))) (negative_sqrt f (.- (three f))))
    tmp1 tmp2 tmp3, 
end 

/- Now we do uniqueness. As every cubic is equivalent to a depressed cubic, it is sufficient to prove 
     this for the general depressed cubic.-/ 

lemma depressed_cubic_factorize (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f]
    (c d x : f) (c_ne_zero : c ≠ myfld.zero) :
  (depressed_cubic_subst f c d x) = 
    (factorized_cubic_expression f x
                                  (cardano_formula_a f c d c_ne_zero) 
                                  (cardano_formula_b f c d c_ne_zero) 
                                  (cardano_formula_c f c d c_ne_zero))
  :=
begin
  rw multiply_out_cubic f x _ _ _, 
    rw cardano_formulae_sum_zero f, rw mul_zero f (x .* x), 
    rw negate_zero_zero f, rw simp_zero f, 
    rw cardano_products f c d x c_ne_zero, 
    rw cardano_product f, rw double_negative f d, 
    unfold depressed_cubic_subst, rw myfld.mul_comm x c,
end

lemma cardano_formula_uniqueness (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d x : f) (c_ne_zero : c ≠ myfld.zero) : 
  (x ≠ (cardano_formula_a f c d c_ne_zero)) -> 
  (x ≠ (cardano_formula_b f c d c_ne_zero)) -> 
  (x ≠ (cardano_formula_c f c d c_ne_zero)) -> 
  ((depressed_cubic_subst f c d x) ≠ myfld.zero) := 
begin 
  have h : factorized_cubic_expression f x (cardano_formula_a f c d c_ne_zero) (cardano_formula_b f c d c_ne_zero) (cardano_formula_c f c d c_ne_zero)
        = depressed_cubic_subst f c d x, 
    symmetry, exact depressed_cubic_factorize f c d x c_ne_zero,

  intros not_formula_a not_formula_b not_formula_c solution, 
  unfold factorized_cubic_expression at h, rw solution at h, 
  have ne_zero_a : (x .+ (.- (cardano_formula_a f c d c_ne_zero))) ≠ myfld.zero, 
    exact subtract_ne f x (cardano_formula_a f c d c_ne_zero) not_formula_a, 
  have ne_zero_b : (x .+ (.- (cardano_formula_b f c d c_ne_zero))) ≠ myfld.zero, 
    exact subtract_ne f x (cardano_formula_b f c d c_ne_zero) not_formula_b, 
  have ne_zero_c : (x .+ (.- (cardano_formula_c f c d c_ne_zero))) ≠ myfld.zero, 
    exact subtract_ne f x (cardano_formula_c f c d c_ne_zero) not_formula_c, 

  exact (mul_nonzero f ((x .+ (.- (cardano_formula_a f c d c_ne_zero))) .* (x .+ (.- (cardano_formula_b f c d c_ne_zero)))) (x .+ (.- (cardano_formula_c f c d c_ne_zero))) (mul_nonzero f (x .+ (.- (cardano_formula_a f c d c_ne_zero))) (x .+ (.- (cardano_formula_b f c d c_ne_zero))) ne_zero_a ne_zero_b) ne_zero_c)
        h,
end 

lemma cubic_formula_uniqueness (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (a1 b c d x : f) (a_ne_zero : a1 ≠ myfld.zero) (int_quantity_ne_zero : ((three f) .* (a1 .* c)) .+ (.- (square f b)) ≠ myfld.zero) : 
  (x ≠ (cubic_formula_a f a1 b c d a_ne_zero int_quantity_ne_zero)) -> 
  (x ≠ (cubic_formula_b f a1 b c d a_ne_zero int_quantity_ne_zero)) -> 
  (x ≠ (cubic_formula_c f a1 b c d a_ne_zero int_quantity_ne_zero)) -> 
  ((cubic_subst f a1 b c d x) ≠ myfld.zero) := 
begin 
  intros ha hb hc, 
  have move_term : ∀ (q : f), 
        x ≠ q .+ (.- ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) <-> 
        (x .+ ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) ≠ q, 
    intros q, split, 
      intros h1 h2, rw <- h2 at h1, clear h2, rw <- myfld.add_assoc at h1, 
      rw myfld.add_negate at h1, rw zero_simp f x at h1, cc, 

      intros h1 h2, rw h2 at h1, clear h2, rw <- myfld.add_assoc at h1, rw myfld.add_comm (.- _) _ at h1, 
      rw myfld.add_negate at h1, rw zero_simp f q at h1, cc, 

  unfold cubic_formula_a at ha, rw move_term _ at ha, 
  unfold cubic_formula_b at hb, rw move_term _ at hb, 
  unfold cubic_formula_c at hc, rw move_term _ at hc, 

  intros is_solution, rw divide_cubic_through f a1 b c d _ a_ne_zero at is_solution, 
  have tmp : x = (x .+ ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) .+ (.- ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) , 
    rw <- myfld.add_assoc, rw myfld.add_negate, exact myfld.add_zero x, 
  rw (reduce_cubic_to_depressed f (b .* (myfld.reciprocal a1 a_ne_zero)) (c .* (myfld.reciprocal a1 a_ne_zero)) (d .* (myfld.reciprocal a1 a_ne_zero)) x (x .+ ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) tmp) at is_solution, 
  exact cardano_formula_uniqueness f _ _ _ (int_quantity_ne_zero_simp f a1 b c a_ne_zero int_quantity_ne_zero) ha hb hc is_solution, 
end 

lemma cubic_formula_alt_uniqueness (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (a1 b c d x : f) (a_ne_zero : a1 ≠ myfld.zero) (int_quantity_eq_zero : ((three f) .* (a1 .* c)) .+ (.- (square f b)) = myfld.zero) : 
  (x ≠ (cubic_formula_a_alt f a1 b c d a_ne_zero int_quantity_eq_zero)) -> 
  (x ≠ (cubic_formula_b_alt f a1 b c d a_ne_zero int_quantity_eq_zero)) -> 
  (x ≠ (cubic_formula_c_alt f a1 b c d a_ne_zero int_quantity_eq_zero)) -> 
  ((cubic_subst f a1 b c d x) ≠ myfld.zero) := 
begin 
  intros ha hb hc is_solution, rw divide_cubic_through f a1 b c d _ a_ne_zero at is_solution, 
  have tmp : x = (x .+ ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) .+ (.- ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) , 
    rw <- myfld.add_assoc, rw myfld.add_negate, exact myfld.add_zero x, 
  rw (reduce_cubic_to_depressed f (b .* (myfld.reciprocal a1 a_ne_zero)) (c .* (myfld.reciprocal a1 a_ne_zero)) (d .* (myfld.reciprocal a1 a_ne_zero)) x (x .+ ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) tmp) at is_solution, 
  rw (int_quantity_eq_zero_simp f a1 b c a_ne_zero int_quantity_eq_zero) at is_solution, 
  unfold depressed_cubic_subst at is_solution, 
  rw mul_zero at is_solution, rw simp_zero at is_solution, 

  have move_term : ∀ (q : f), 
        x ≠ q .+ (.- ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) <-> 
        (x .+ ((b .* (myfld.reciprocal a1 a_ne_zero)) .* (third f))) ≠ q, 
    intros q, split, 
      intros h1 h2, rw <- h2 at h1, clear h2, rw <- myfld.add_assoc at h1, 
      rw myfld.add_negate at h1, rw zero_simp f x at h1, cc, 

      intros h1 h2, rw h2 at h1, clear h2, rw <- myfld.add_assoc at h1, rw myfld.add_comm (.- _) _ at h1, 
      rw myfld.add_negate at h1, rw zero_simp f q at h1, cc, 

  unfold cubic_formula_a_alt at ha, rw move_term _ at ha, 
    unfold depressed_cubic_solution_c_zero_a at ha, unfold depressed_cubic_solution_c_zero at ha, 
    rw move_negation_ne f _ _ at ha, 
  unfold cubic_formula_b_alt at hb, rw move_term _ at hb, 
    unfold depressed_cubic_solution_c_zero_b at hb, unfold depressed_cubic_solution_c_zero at hb, 
    rw move_negation_ne f _ _ at hb, 
  unfold cubic_formula_c_alt at hc, rw move_term _ at hc, 
    unfold depressed_cubic_solution_c_zero_c at hc, unfold depressed_cubic_solution_c_zero at hc, 
    rw move_negation_ne f _ _ at hc, 
  clear move_term, clear tmp, 
  rw move_across at is_solution, 
  have tmp : ∀ (x : f), .- (cubed f x) = cubed f (.- x), 
    intros q, unfold cubed, simp, 
  rw tmp _ at is_solution, 
  exact (no_other_cubrts_simple f _ _ ha hb hc) is_solution, 
end 
