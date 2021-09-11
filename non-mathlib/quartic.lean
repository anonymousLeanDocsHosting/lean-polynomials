import field_definition
import field_results
import numbers
import roots
import quadratic 
import cubic 

lemma not_char_four (f : Type) [myfld f] [fld_not_char_two f] : 
    (four f) ≠ myfld.zero := 
begin 
  unfold four, rw two_plus_two f, 
  exact mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two, 
end 

def fourth_power (f : Type) [myfld f] (a : f) : f := 
  a .* (a .* (a .* a))

lemma fourth_power_of_product (f : Type) [myfld f] (a b : f) : 
  (fourth_power f (a .* b)) = (fourth_power f a) .* (fourth_power f b) := 
begin 
  unfold fourth_power, repeat {rw <- myfld.mul_assoc}, 
  repeat {rw myfld.mul_comm b (_ .* _) }, repeat {rw <- myfld.mul_assoc}, 
end 

lemma fourth_power_negate (f : Type) [myfld f] (a : f) : 
  (fourth_power f (.- a)) = (fourth_power f a) := 
begin 
  unfold fourth_power, repeat {rw mul_negate}, repeat {rw mul_negate_alt_simp}, repeat {rw double_negative}, 
end 

def fourth_root_a (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : f := 
  (sqroot (sqroot a))

lemma fourth_root_to_power_a (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : 
  fourth_power f (fourth_root_a f a) = a := 
begin 
  unfold fourth_power, unfold fourth_root_a, 
  rw fld_with_sqrt.sqrt_mul_sqrt (sqroot a), 
  rw myfld.mul_assoc, rw fld_with_sqrt.sqrt_mul_sqrt (sqroot a), 
  rw fld_with_sqrt.sqrt_mul_sqrt a, 
end 

def fourth_root_b (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : f := 
  (.- (sqroot (sqroot a)))

lemma fourth_root_to_power_b (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : 
  fourth_power f (fourth_root_b f a) = a := 
begin 
  unfold fourth_power, unfold fourth_root_b, 
  repeat {rw mul_negate_alt_simp, rw mul_negate}, 
  repeat {rw mul_negate_alt_simp}, repeat {rw double_negative}, 
  rw fld_with_sqrt.sqrt_mul_sqrt (sqroot a), 
  rw myfld.mul_assoc, rw fld_with_sqrt.sqrt_mul_sqrt (sqroot a), 
  rw fld_with_sqrt.sqrt_mul_sqrt a, 
end 

def fourth_root_c (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : f := 
  sqroot (.- (sqroot a))

lemma fourth_root_to_power_c (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : 
  fourth_power f (fourth_root_c f a) = a := 
begin 
  unfold fourth_power, unfold fourth_root_c, 
  rw fld_with_sqrt.sqrt_mul_sqrt (.- (sqroot a)), 
  rw myfld.mul_assoc, rw fld_with_sqrt.sqrt_mul_sqrt (.- (sqroot a)), 
  rw mul_negate, rw mul_negate_alt_simp, 
  rw fld_with_sqrt.sqrt_mul_sqrt a, rw double_negative, 
end 

def fourth_root_d (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : f := 
  .- (sqroot (.- (sqroot a)))

lemma fourth_root_to_power_d (f : Type) [myfld f] [fld_with_sqrt f] (a : f) : 
  fourth_power f (fourth_root_d f a) = a := 
begin 
  unfold fourth_power, unfold fourth_root_d, 
  repeat {rw mul_negate_alt_simp, rw mul_negate}, 
  repeat {rw mul_negate_alt_simp}, repeat {rw double_negative}, 
  rw fld_with_sqrt.sqrt_mul_sqrt (.- (sqroot a)), 
  rw myfld.mul_assoc, rw fld_with_sqrt.sqrt_mul_sqrt (.- (sqroot a)), 
  rw mul_negate, rw mul_negate_alt_simp, 
  rw fld_with_sqrt.sqrt_mul_sqrt a, rw double_negative, 
end 

/- We put the negations in this expression so that it represents the quartic who's 
    solutions are a1 a2 a3 & a4, which is neat.-/ 
def factorized_quartic_expression (f : Type) [myfld f] (x a1 a2 a3 a4 : f) : f := 
   ((x .+ (.- a1)) .* ((x .+ (.- a2)) .* ((x .+ (.- a3)) .* (x .+ (.- a4)))))


def quartic_expression (f : Type) [myfld f] (x a b c d e : f) : f := 
  (((fourth_power f x) .* a) .+ (((cubed f x) .* b) .+ (((square f x) .* c) .+ ((x .* d) .+ e))))

lemma multiply_out_quartic (f : Type) [myfld f] (x a1 a2 a3 a4 : f) : 
  (factorized_quartic_expression f x a1 a2 a3 a4) = 
  (quartic_expression f x myfld.one (.- (a1 .+ (a2 .+ (a3 .+ a4)))) ((a1 .* a2) .+ ((a1 .* a3) .+ ((a1 .* a4) .+ ((a2 .* a3) .+ ((a2 .* a4) .+ (a3 .* a4)))))) (.- ((a1 .* (a2 .* a3)) .+ ((a1 .* (a2 .* a4)) .+ ((a1 .* (a3 .* a4)) .+ (a2 .* (a3 .* a4)))))) (a1 .* (a2 .* (a3 .* a4)))) := 
begin 
  have clear_term : ∀ (a b x : f), a = b -> (x .+ a) = (x .+ b), 
    intros a b x h, rw h, 
  unfold quartic_expression, unfold factorized_quartic_expression, 
  unfold fourth_power, unfold cubed, unfold square, 
  repeat {rw distrib_simp f _ _ _}, repeat {rw distrib_simp_alt f _ _ _}, 
  repeat {rw distrib_simp f _ _ _}, repeat {rw distrib_simp_alt f _ _ _}, 
  repeat {rw mul_negate_alt_simp f _ _}, repeat {rw mul_negate f _ _}, 
  repeat {rw mul_negate_alt_simp f _ _}, repeat {rw mul_negate f _ _}, 
  repeat {rw double_negative f _}, 
  repeat {rw distrib_simp_alt f}, 
  repeat {rw <- myfld.add_assoc}, repeat {rw myfld.mul_assoc}, repeat {rw add_negate f}, 
  rw simp_mul_one, 
  apply clear_term _ _ _, 
  repeat {rw myfld.add_assoc}, rw myfld.add_comm _ (.- (((x .* x) .* x) .* a4)), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  rw <- myfld.mul_assoc (x .* x) a3 x, rw myfld.mul_comm a3 x, rw myfld.mul_assoc (x .* x) x a3, 
  repeat {rw myfld.add_assoc}, rw myfld.add_comm _ (.- (((x .* x) .* x) .* a3)), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  repeat {rw myfld.add_assoc}, rw myfld.add_comm _ (((x .* x) .* a3) .* a4), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  rw myfld.mul_comm ((x .* x) .* x) a2, rw myfld.mul_comm x a2, repeat {rw myfld.mul_assoc}, 
  repeat {rw myfld.add_assoc}, rw myfld.add_comm _ (.- (((a2 .* x) .* x) .* x)), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  repeat {rw myfld.add_assoc}, repeat {rw myfld.add_comm _ (((a1 .* a2) .* a3) .* a4) }, 
  apply clear_term _ _ _, 
  rw myfld.mul_comm (x .* x) a2, repeat {rw myfld.mul_assoc}, rw myfld.add_comm _ (((a2 .* x) .* x) .* a4), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  rw <- myfld.mul_assoc (a2 .* x) x a3, rw myfld.mul_comm x a3, rw myfld.mul_assoc (a2 .* x) a3 x, 
  repeat {rw myfld.add_assoc}, rw myfld.add_comm _ (((a2 .* x) .* a3) .* x), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  rw myfld.add_comm _ (_ .+ _), rw myfld.mul_comm ((x .* x) .* x) a1, repeat {rw myfld.mul_assoc}, 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  rw myfld.mul_comm (x .* x) a1, rw myfld.mul_assoc a1 x x, 
  repeat {rw myfld.add_assoc}, rw myfld.add_comm _ (((a1 .* x) .* x) .* a4), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  rw <- myfld.mul_assoc (a1 .* x) x a3, rw myfld.mul_comm x a3, rw myfld.mul_assoc (a1 .* x) a3 x, 
  repeat {rw myfld.add_assoc}, rw myfld.add_comm _ (((a1 .* x) .* a3) .* x), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  rw myfld.mul_comm x a1, 
  repeat {rw myfld.add_assoc}, rw myfld.add_comm _ (.- (((a1 .* x) .* a3) .* a4)), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  rw myfld.mul_comm ((a1 .* x) .* x) a2, rw myfld.mul_comm a1 a2, repeat {rw myfld.mul_assoc}, 
  apply clear_term _ _ _, 
  rw myfld.mul_comm (a1 .* x) a2, repeat {rw myfld.mul_assoc}, 
  repeat {rw myfld.add_assoc}, rw myfld.add_comm _ (.- (((a2 .* a1) .* x) .* a4)), 
  repeat {rw <- myfld.add_assoc}, apply clear_term _ _ _, 
  repeat {rw myfld.mul_comm (_ .* _) x}, repeat {rw myfld.mul_assoc}, 
end 

lemma multiply_out_fourth_power (f : Type) [myfld f] (x y : f) : 
  (fourth_power f (x .+ y)) = 
  quartic_expression f x myfld.one 
                    ((four f) .* y)
                    ((six f) .* (square f y))
                    ((four f) .* (cubed f y))
                    (fourth_power f y) := 
begin 
  have reduce : (fourth_power f (x .+ y)) = 
                factorized_quartic_expression f x (.- y) (.- y) (.- y) (.- y), 
    unfold factorized_quartic_expression, unfold fourth_power, repeat {rw double_negative f y}, 
  rw reduce, clear reduce, rw multiply_out_quartic, 
  simp only [mul_negate, mul_negate_alt_simp, double_negative], 
  repeat {rw <- add_negate f _ _}, repeat {rw double_negative f _}, 
  have equate_coeff : ∀ (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 x : f), 
                      (a1 = a2) -> (b1 = b2) -> (c1 = c2) -> (d1 = d2) -> (e1 = e2) -> 
                      (quartic_expression f x a1 b1 c1 d1 e1) = (quartic_expression f x a2 b2 c2 d2 e2), 
    intros a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 x h1 h2 h3 h4 h5, rw h1, rw h2, rw h3, rw h4, rw h5, 
  apply equate_coeff, 
    refl, 
    unfold four, unfold two, simp, 
    unfold six, unfold two, unfold three, unfold square, simp, 
    unfold four, unfold two, unfold cubed, simp, 
    unfold fourth_power, 
end 

lemma sum_of_fourth_roots (f : Type) [myfld f] [fld_with_sqrt f] (x : f) : 
  (fourth_root_a f x) .+ ((fourth_root_b f x) .+ ((fourth_root_c f x) .+ (fourth_root_d f x))) = 
  myfld.zero := 
begin 
  unfold fourth_root_a fourth_root_b fourth_root_c fourth_root_d, 
  simp, 
end 

lemma no_other_fourth_roots (f : Type) [myfld f] [fld_with_sqrt f] (x root : f) : 
  (root ≠ (fourth_root_a f x)) -> 
  (root ≠ (fourth_root_b f x)) -> 
  (root ≠ (fourth_root_c f x)) -> 
  (root ≠ (fourth_root_d f x)) -> 
  (fourth_power f root) ≠ x := 
begin 
  intros ha hb hc hd is_root, 
  have make_ne_zero : ∀ (a b : f), a ≠ b -> (a .+ (.- b)) ≠ myfld.zero, 
    intros a b h1 h2, have h3 : (a .+ (.- b)) .+ b = myfld.zero .+ b,
      rw h2, clear h2, 
    rw simp_zero at h3, rw <- myfld.add_assoc at h3, rw myfld.add_comm (.- b) b at h3, 
    rw myfld.add_negate b at h3, rw zero_simp at h3, cc, 
  have ha1 : root .+ (.- (fourth_root_a f x)) ≠ myfld.zero, 
    exact make_ne_zero _ _ ha, clear ha, rename ha1 ha, 
  have hb1 : root .+ (.- (fourth_root_b f x)) ≠ myfld.zero, 
    exact make_ne_zero _ _ hb, clear hb, rename hb1 hb, 
  have hc1 : root .+ (.- (fourth_root_c f x)) ≠ myfld.zero, 
    exact make_ne_zero _ _ hc, clear hc, rename hc1 hc, 
  have hd1 : root .+ (.- (fourth_root_d f x)) ≠ myfld.zero, 
    exact make_ne_zero _ _ hd, clear hd, rename hd1 hd, 
  clear make_ne_zero, 

  have multiply_out : factorized_quartic_expression f root (fourth_root_a f x) (fourth_root_b f x) (fourth_root_c f x) (fourth_root_d f x)
                        = (fourth_power f root) .+ (.- x) , 
    rw multiply_out_quartic, 
    rw sum_of_fourth_roots, rw negate_zero_zero, 
    unfold fourth_root_a, unfold fourth_root_b, unfold fourth_root_c, unfold fourth_root_d, 
    repeat {rw mul_negate}, repeat {rw mul_negate_alt_simp}, 
    repeat {rw fld_with_sqrt.sqrt_mul_sqrt}, 
    repeat {rw mul_negate}, repeat {rw mul_negate_alt_simp}, 
    repeat {rw myfld.add_assoc _ (.- _) _}, rw myfld.add_comm (.- _) _, 
    repeat {rw myfld.add_negate}, repeat {rw double_negative}, 
    rw simp_zero, 
    rw myfld.add_comm (.- _) (_ .* _), repeat {rw myfld.add_negate _}, rw simp_zero, 
    rw myfld.add_negate _, rw simp_zero, 
    rw myfld.add_negate _, rw negate_zero_zero, 
    rw myfld.mul_assoc, rw fld_with_sqrt.sqrt_mul_sqrt, rw fld_with_sqrt.sqrt_mul_sqrt, 
    unfold quartic_expression, simp, 

  have h : (fourth_power f root) .+ (.- x) = myfld.zero, 
    rw is_root, exact myfld.add_negate x, 
  rw h at multiply_out, clear h, clear is_root, 

  have h : factorized_quartic_expression f root (fourth_root_a f x) (fourth_root_b f x) (fourth_root_c f x) (fourth_root_d f x)
              ≠ myfld.zero, 
    unfold factorized_quartic_expression, 
    exact mul_nonzero f _ _ ha (mul_nonzero f _ _ hb (mul_nonzero f _ _ hc hd)), 
  cc, 
end 

lemma remove_fourth_power_coefficient (f : Type) [myfld f] (a b c d e x : f) (a_ne_zero : a ≠ myfld.zero) : 
  quartic_expression f x a b c d e = myfld.zero <-> 
   quartic_expression f x myfld.one (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero))
                                    (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero))
                  = myfld.zero := 
begin 
  split, 
    intros h, unfold quartic_expression, 
    have tmp : myfld.one = (a .* (myfld.reciprocal a a_ne_zero)), 
          symmetry, exact myfld.mul_reciprocal a a_ne_zero, 
    rw tmp, clear tmp, 
    repeat {rw myfld.mul_assoc _ _ (myfld.reciprocal a a_ne_zero) }, 
    repeat {rw <- distrib_simp f _ _ (myfld.reciprocal a a_ne_zero) }, 
    unfold quartic_expression at h, rw h, 
    rw mul_zero, 

    intros h, 
    have h1 : (quartic_expression f x myfld.one (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero))) .* a
                = myfld.zero, 
      rw h, exact mul_zero f _, clear h, rename h1 h, 
    unfold quartic_expression at h, 
    repeat {rw distrib_simp f _ _ a at h}, repeat {rw <- myfld.mul_assoc _ _ _ at h}, 
    repeat {rw myfld.mul_comm (myfld.reciprocal a _) a at h}, 
    repeat {rw myfld.mul_reciprocal a a_ne_zero at h}, 
    repeat {rw simp_mul_one at h}, rw one_mul_simp at h, 
    unfold quartic_expression, exact h, 
end 

def depressed_quartic_subst (f : Type) [myfld f] (c d e x : f) : f := 
  ((fourth_power f x) .+ ((c .* (square f x)) .+ ((d .* x) .+ e)))

open nat 

/- Various different powers of two are utilized in the definition of the solution to 
     a quartic, so it's cleaner to have a consistent function to generate them.-/ 
def pow_of_two (f : Type) [myfld f] : nat -> f 
| 0 := myfld.one 
| (succ n) := (pow_of_two n) .* (two f)

lemma pow_of_two_nonzero (f : Type) [myfld f] [fld_not_char_two f] (exp : nat) : 
    (pow_of_two f exp ≠ myfld.zero) := 
begin 
  induction exp, 
    unfold pow_of_two, exact myfld.zero_distinct_one, 

    unfold pow_of_two, exact mul_nonzero f (pow_of_two f exp_n) (two f) exp_ih fld_not_char_two.not_char_two, 
end 

def depressed_quartic_squ_coeff (f : Type) [myfld f] [fld_not_char_two f] (b c : f) : f := 
    (c .+ (.- ((square f b) .* ((three f) .* (myfld.reciprocal (pow_of_two f 3) (pow_of_two_nonzero f 3))))))

def depressed_quartic_linear_coeff (f : Type) [myfld f] [fld_not_char_two f] (b c d : f) : f := 
  ((((cubed f b) .* (myfld.reciprocal (pow_of_two f 3) (pow_of_two_nonzero f 3))) .+ (.- ((b .* c) .* (myfld.reciprocal (two f) fld_not_char_two.not_char_two)))) .+ d)

def depressed_quartic_constant (f : Type) [myfld f] [fld_not_char_two f] (b c d e : f) : f := 
  ((((.- ((fourth_power f b) .* ((three f) .* (myfld.reciprocal (pow_of_two f 8) (pow_of_two_nonzero f 8))))) .+ ((c .* (square f b)) .* (myfld.reciprocal (pow_of_two f 4) (pow_of_two_nonzero f 4)))) .+ (.- ((b .* d) .* (myfld.reciprocal (four f) (four_ne_zero f))))) .+ e)


/- The first of a few tedious helper lemmae that we use to expediate the proof of reducing 
a quartic function to a depressed quartic.-/ 

/- lemma six_div_sixteen (f : Type) [myfld f] [fld_not_char_two f] : 
  ((six f) .* (myfld.reciprocal (square f (four f)) (square_ne_zero f (four f) (four_ne_zero f))))
  = ((three f) .* (myfld.reciprocal (pow_of_two f 3) (pow_of_two_nonzero f 3))) := 
begin 
  unfold six, unfold four, unfold square, unfold pow_of_two, 
  rw split_reciprocal, 
  rw reciprocal_rewrite f ((two f) .+ (two f)) ((two f) .* (two f)) (two_plus_two f) _, 
  rw [split_reciprocal f (two f) (two f) _] {occs := occurrences.pos [1]}, 
  rw myfld.mul_comm (two f) (three f), 
  repeat {rw <- myfld.mul_assoc}, rw myfld.mul_assoc (two f) (myfld.reciprocal (two f) _) _, 
  rw myfld.mul_reciprocal (two f) _, rw one_mul_simp, 
  repeat {rw split_reciprocal}, rw recip_one_one, rw one_mul_simp, 
  repeat {rw myfld.mul_assoc}, 
end -/ 

lemma quartic_reduce_x_squ_helper (f : Type) [myfld f] [fld_not_char_two f] (b c : f) : 
  ((.- ((three f) .* (b .* ((myfld.reciprocal (four f) (four_ne_zero f)) .* b)))) .+ (c .+ ((six f) .* ((myfld.reciprocal (square f (four f)) (square_ne_zero f (four f) (four_ne_zero f))) .* (square f b))))) = 
    (depressed_quartic_squ_coeff f b c) := 
begin 
  have clear_term : ∀ (a b x : f), a = b -> (x .+ a) = (x .+ b), 
    intros a b x h, rw h, 
  unfold depressed_quartic_squ_coeff, 
  rw myfld.add_assoc _ c _, rw myfld.add_comm _ c, rw <- myfld.add_assoc c _ _, 
  apply clear_term _ _ c, clear clear_term, 
  have clear_term : ∀ (a b x : f), a = b -> (x .* a) = (x .* b), 
    intros a b x h, rw h, 
  unfold six, rw myfld.mul_comm (two f) (three f), rw <- myfld.mul_assoc (three f) _ _, 
  rw mul_negate_alt f (three f) _, rw <- distrib_simp_alt f (three f) _ _, 
  rw myfld.mul_assoc (square f b) (three f) _, rw myfld.mul_comm (square f b) (three f), rw <- myfld.mul_assoc (three f) _ _, 
  rw mul_negate_alt f (three f) _, 
  apply clear_term _ _ (three f), 
  rw myfld.mul_comm (myfld.reciprocal _ _) b, rw myfld.mul_assoc b b _, rw mul_negate_alt f (b .* b) _, 
  rw myfld.mul_assoc (two f) (myfld.reciprocal _ _) _, rw myfld.mul_comm _ (square f b), 
  unfold square, rw <- distrib_simp_alt f (b .* b) _ _, 
  rw mul_negate_alt f (b .* b) _, 
  apply clear_term _ _ (b .* b), 
  rw split_reciprocal f (four f) (four f) _, unfold four, 
  rw reciprocal_rewrite f ((two f) .+ (two f)) ((two f) .* (two f)) (two_plus_two f) _, 
  rw [split_reciprocal f (two f) (two f) _] {occs := occurrences.pos [2]}, 
  repeat {rw myfld.mul_assoc}, rw myfld.mul_reciprocal (two f) _, rw one_mul_simp, 
  rw [myfld.mul_one (myfld.reciprocal ((two f) .* (two f)) _) ] {occs := occurrences.pos [1]}, 
  rw myfld.mul_comm (myfld.reciprocal _ _) (myfld.reciprocal _ _), rw mul_negate_alt f _ myfld.one, 
  rw <- distrib_simp_alt f _ _ _, 
  have tmp : myfld.one = (two f) .* (myfld.reciprocal (two f) (two_ne_zero f)) , 
    rw myfld.mul_reciprocal (two f), 
  rw tmp, clear tmp, 
  rw [myfld.mul_one (myfld.reciprocal (two f) _) ] {occs := occurrences.pos [2]}, 
  rw myfld.mul_comm (two f) (myfld.reciprocal _ _), rw mul_negate_alt, 
  rw <- distrib_simp_alt, 
  have tmp : .- (two f) = (.- myfld.one) .+ (.- myfld.one) , 
    unfold two, simp, 
  rw tmp, clear tmp, rw <- myfld.add_assoc _ (.- myfld.one) myfld.one, 
  rw myfld.add_comm (.- myfld.one) myfld.one, rw myfld.add_negate myfld.one, 
  rw zero_simp, unfold pow_of_two, simp, 
end 

lemma quartic_reduce_linear_helper (f : Type) [myfld f] [fld_not_char_two f] (b c d : f) : 
  ((((.- ((two f) .* (b .* ((myfld.reciprocal (four f) (four_ne_zero f)) .* c)))) .+ d) .+ (.- ((four f) .* (cubed f ((myfld.reciprocal (four f) (four_ne_zero f)) .* b))))) .+ ((three f) .* (b .* ((myfld.reciprocal (four f) (four_ne_zero f)) .* (b .* ((myfld.reciprocal (four f) (four_ne_zero f)) .* b))))))
    = depressed_quartic_linear_coeff f b c d := 
begin 
  unfold depressed_quartic_linear_coeff, 
  have clear_term : ∀ (a b x : f), a = b -> (x .+ a) = (x .+ b), 
    intros a b x h, rw h, 
  repeat {rw myfld.add_comm _ d}, repeat {rw <- myfld.add_assoc}, 
  apply clear_term _ _ d, 
  rw myfld.mul_comm (myfld.reciprocal _ _) c, rw myfld.mul_assoc b c _, 
  rw myfld.mul_assoc _ (b .* c) _, rw myfld.mul_comm _ (b .* c), rw <- myfld.mul_assoc (b .* c) _ _, 
  unfold four, 
  rw reciprocal_rewrite f ((two f) .+ (two f)) ((two f) .* (two f)) (two_plus_two f) _, 
  rw [split_reciprocal f (two f) (two f) _] {occs := occurrences.pos [1]}, 
  rw myfld.mul_assoc (two f) (myfld.reciprocal _ _) (myfld.reciprocal _ _), 
  rw myfld.mul_reciprocal (two f) _, rw one_mul_simp, 
  rw only_one_reciprocal f (two f) _ fld_not_char_two.not_char_two, 
  rw myfld.add_comm ((cubed f b) .* _) _, 
  apply clear_term, clear clear_term, 
  have cube_of_product : ∀ (x y : f), (cubed f (x .* y)) = (cubed f x) .* (cubed f y) , 
    unfold cubed, intros x y, repeat {rw myfld.mul_assoc}, 
    repeat {rw myfld.mul_comm (_ .* _) x}, repeat {rw myfld.mul_assoc}, 
  rw cube_of_product, clear cube_of_product, 
  rw only_one_reciprocal f ((two f) .* (two f)) _ (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two), 
  repeat {rw myfld.mul_comm (_ .* _) b}, repeat {rw myfld.mul_comm (myfld.reciprocal _ _) b}, 
  repeat {rw myfld.mul_assoc}, 
  rw myfld.mul_comm (_ .* _) b, rw myfld.mul_assoc b (b .* b) _, 
  repeat {rw <- myfld.mul_assoc (b .* (b .* b)) _ _}, 
  rw myfld.mul_comm _ (cubed f b), unfold cubed, 
  rw mul_negate_alt f (b .* (b .* b)) _, 
  rw <- distrib_simp_alt f (b .* (b .* b)) _ _, 
  have clear_term : ∀ (a b x : f), a = b -> (x .* a) = (x .* b), 
    intros a b x h, rw h, 
  apply clear_term, 
  rw two_plus_two f, rw myfld.mul_assoc ((two f) .* (two f)) (myfld.reciprocal _ _) _, 
  rw myfld.mul_reciprocal ((two f) .* (two f)) _, rw one_mul_simp, 
  rw mul_negate_alt f (myfld.reciprocal _ _) (myfld.reciprocal _ _), 
  rw myfld.mul_comm (three f) _, rw <- myfld.mul_assoc _ (three f) _, 
  rw <- distrib_simp_alt, 
  unfold pow_of_two, repeat {rw <- reciprocal_rewrite f _ _ (myfld.mul_assoc _ _ _) _}, 
  rw reciprocal_rewrite f _ _ (one_mul_simp f _) _, 
  rw reciprocal_rewrite f _ _ (myfld.mul_assoc _ _ _) _, 
  rw split_reciprocal f ((two f) .* (two f)) (two f) _, 
  rw only_one_reciprocal f ((two f) .* (two f)) _ (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two), 
  apply clear_term, 
  have tmp : ∀ (x : f), (.- x) = (.- (myfld.one)) .* x,
    intros x, simp, 
  rw tmp, clear tmp, rw <- distrib_simp f _ _ _, 
  unfold three, rw myfld.add_assoc (.- myfld.one) myfld.one _, rw myfld.add_comm (.- myfld.one) myfld.one, 
  rw myfld.add_negate myfld.one, rw simp_zero, 
  have tmp : (myfld.one .+ myfld.one) = (two f), unfold two, rw tmp, clear tmp, 
  rw split_reciprocal f (two f) (two f) _, rw myfld.mul_assoc, rw myfld.mul_reciprocal, 
  rw only_one_reciprocal f (two f) _ fld_not_char_two.not_char_two, rw one_mul_simp, 
  apply mul_nonzero f, 
  exact myfld.zero_distinct_one, apply mul_nonzero f, 
  exact fld_not_char_two.not_char_two, 
  exact (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two), 
end 

lemma quartic_reduce_constant_helper (f : Type) [myfld f] [fld_not_char_two f] (b c d e : f) : 
  (fourth_power f (.- ((myfld.reciprocal (four f) (four_ne_zero f)) .* b))) .+ ((.- ((cubed f ((myfld.reciprocal (four f) (four_ne_zero f)) .* b)) .* b)) .+ (((myfld.reciprocal (square f (four f)) (square_ne_zero f (four f) (four_ne_zero f))) .* ((square f b) .* c)) .+ ((.- (b .* ((myfld.reciprocal (four f) (four_ne_zero f)) .* d))) .+ e)))
        = depressed_quartic_constant f b c d e := 
begin 
  have clear_term : ∀ (a b x : f), a = b -> (x .+ a) = (x .+ b), 
    intros a b x h, rw h, 
  unfold depressed_quartic_constant, 
  repeat {rw myfld.add_assoc}, repeat {rw myfld.add_comm _ e}, apply clear_term, 
  rw myfld.mul_comm (myfld.reciprocal _ _) d, rw myfld.mul_assoc b d _, 
  repeat {rw myfld.add_comm _ (.- ((b .* d) .* (myfld.reciprocal (four f) _))) }, 
  apply clear_term, 
  have tmp : (square f (four f)) = (pow_of_two f 4), 
    unfold four, rw two_plus_two, unfold square, unfold pow_of_two, rw one_mul_simp, repeat {rw myfld.mul_assoc}, 
  rw reciprocal_rewrite f _ _ tmp _, 
  rw <- myfld.mul_assoc _ (square f b) c, rw myfld.mul_comm (square f b) c, 
  rw myfld.mul_comm (myfld.reciprocal _ _) (c .* (square f b)), 
  repeat {rw myfld.add_comm _ ((c .* (square f b)) .* (myfld.reciprocal (pow_of_two f 4) _)) }, 
  apply clear_term, clear clear_term, clear tmp, 
  rw cube_of_product, rw fourth_power_negate, rw fourth_power_of_product, 
  rw <- myfld.mul_assoc _ (cubed f b) b, rw myfld.mul_comm _ ((cubed f b) .* b), 
  have tmp : ((cubed f b) .* b) = fourth_power f b, unfold cubed, unfold fourth_power, repeat {rw myfld.mul_assoc}, 
  rw tmp, clear tmp, rw mul_negate_alt f (fourth_power f b) _, rw myfld.mul_comm _ (fourth_power f b), 
  rw <- distrib_simp_alt f (fourth_power f b) _, 
  repeat {rw <- myfld.mul_assoc (fourth_power f b) _ _}, 
  rw mul_negate_alt f (fourth_power f b) _, 
  have clear_term : ∀ (a b x : f), a = b -> (x .* a) = (x .* b), 
    intros a b x h, rw h, 
  apply clear_term, 
  have tmp : (pow_of_two f 8) = (((four f) .* (four f)) .* ((four f) .* (four f))), 
    unfold four, rw two_plus_two, unfold pow_of_two, rw one_mul_simp, repeat {rw myfld.mul_assoc}, 
  rw reciprocal_rewrite f _ _ tmp _, unfold cubed, rw mul_two_reciprocals f (four f) (four f) _, 
  have squ_squ : ∀ (x : f), (fourth_power f x) = ((x .* x) .* (x .* x)), 
    intros x, unfold fourth_power, repeat {rw myfld.mul_assoc}, 
  rw squ_squ, clear squ_squ, rw mul_two_reciprocals f (four f) (four f) _ _, 
  rw myfld.mul_comm (myfld.reciprocal (four f) _) (myfld.reciprocal ((four f) .* (four f)) _), 
  rw myfld.mul_comm (three f) (myfld.reciprocal _ _), 
  rw split_reciprocal f ((four f) .* (four f)) _ _, rw <- myfld.mul_assoc (myfld.reciprocal _ _) _ (three f), 
  repeat {rw mul_negate_alt f (myfld.reciprocal ((four f) .* (four f)) _) _}, 
  rw only_one_reciprocal f ((four f) .* (four f)) _ (mul_nonzero f (four f) (four f) (four_ne_zero f) (four_ne_zero f)), 
  rw <- distrib_simp_alt, apply clear_term, 
  clear tmp, 
  have mul_both_sides : ∀ (x y z : f), (x ≠ myfld.zero) -> (x .* y) = (x .* z) -> y = z, 
    intros x y z h1 h2, have h3 : (myfld.reciprocal x h1) .* (x .* y) = (myfld.reciprocal x h1) .* (x .* z) , 
      rw h2, 
    repeat {rw myfld.mul_assoc at h3}, rw myfld.mul_comm _ x at h3, rw myfld.mul_reciprocal x h1 at h3, 
    repeat {rw one_mul_simp at h3}, exact h3, 
  apply mul_both_sides ((four f) .* (four f)) _ _, 
  exact mul_nonzero f (four f) (four f) (four_ne_zero f) (four_ne_zero f), 
  rw distrib_simp_alt, rw myfld.mul_reciprocal, 
  rw myfld.mul_assoc ((four f) .* (four f)) (myfld.reciprocal _ _) _, 
  rw myfld.mul_reciprocal, rw one_mul_simp, 
  rw mul_negate_alt_simp, rw <- myfld.mul_assoc (four f) (four f) (myfld.reciprocal (four f) _), 
  rw myfld.mul_reciprocal, rw simp_mul_one, 
  unfold four, unfold two, rw <- myfld.add_assoc myfld.one _ _, 
  rw add_negate, rw myfld.add_assoc myfld.one (.- myfld.one) _, 
  rw myfld.add_negate, rw simp_zero, 
  unfold three, 
end 

/- Similarly to how the x^2 term can be removed from a cubic with a clever substitution, the 
    x^3 term can be removed from a quartic.-/ 
lemma reduce_quartic_to_depressed (f : Type) [myfld f] [fld_not_char_two f] (b c d e x u : f) : 
  (x = u .+ (.- (b .* (myfld.reciprocal (four f) (four_ne_zero f))))) -> 
  (quartic_expression f x myfld.one b c d e) = 
  (depressed_quartic_subst f (depressed_quartic_squ_coeff f b c) (depressed_quartic_linear_coeff f b c d) (depressed_quartic_constant f b c d e) u) := 
begin 
  intro hu, rw hu, clear hu, unfold quartic_expression, 
  rw multiply_out_fourth_power, rw multiply_out_cubed, rw multiply_out_squared, 
  unfold quartic_expression, 
  repeat {rw simp_mul_one}, repeat {rw one_mul_simp}, 
  repeat {rw square_negate}, repeat {rw cube_negate}, 
  repeat {rw distrib_simp}, repeat {rw distrib_simp_alt}, 
  repeat {rw mul_negate}, repeat {rw mul_negate_alt_simp}, 
  repeat {rw mul_negate}, repeat {rw mul_negate_alt_simp}, 
  rw mul_negate, 
  repeat {rw double_negative}, 
  repeat {rw <- myfld.add_assoc}, 
  repeat {rw <- myfld.mul_assoc}, 
  have clear_term : ∀ (a b x : f), a = b -> (x .+ a) = (x .+ b), 
    intros a b x h, rw h, 
  unfold depressed_quartic_subst, 

  /- We can clear the u^4 term from both sides.-/ 
  apply clear_term, 

  /- The u^3 term doesn't exist...-/ 
  rw myfld.add_comm ((cubed f u) .* b) _, repeat {rw myfld.add_assoc}, 
  rw myfld.add_comm _ ((cubed f u) .* b), repeat {rw <- myfld.add_assoc}, 
  rw myfld.mul_comm b (myfld.reciprocal (four f) _), rw myfld.mul_assoc (four f) (myfld.reciprocal (four f) _) b, 
  rw myfld.mul_reciprocal (four f) _, rw one_mul_simp, 
  rw myfld.add_assoc ((cubed f u) .* b) (.- ((cubed f u) .* b)), 
  rw myfld.add_negate, rw simp_zero, 

  /- u^2 term...-/ 
  rw <- mul_two_squares f (myfld.reciprocal (four f) _) b, 
  rw reciprocal_squared f (four f) _, rw myfld.mul_assoc (six f) (myfld.reciprocal _ _) _, 
  rw myfld.add_comm ((square f u) .* c) _, repeat {rw myfld.add_assoc}, 
  rw myfld.add_comm _ ((square f u) .* c), repeat {rw <- myfld.add_assoc}, 
  rw myfld.add_assoc ((square f u) .* c) ((square f u) .* _) _, 
  rw <- distrib_simp_alt f (square f u) c _, 
  rw myfld.mul_assoc (three f) (square f u) _, rw myfld.mul_comm (three f) (square f u), repeat {rw <- myfld.mul_assoc}, 
  rw mul_negate_alt f (square f u) _, 
  rw myfld.add_comm ((square f u) .* (.- _)) _, repeat {rw myfld.add_assoc}, 
  rw myfld.add_comm _ ((square f u) .* (.- _)), repeat {rw <- myfld.add_assoc}, 
  rw myfld.add_assoc ((square f u) .* _) ((square f u) .* _) _, 
  rw <- distrib_simp_alt f (square f u) _ _, 
  rw quartic_reduce_x_squ_helper, rw myfld.mul_comm _ (square f u), 
  apply clear_term, 

  /- u term...-/ 
  rw myfld.mul_comm u c, repeat {rw myfld.mul_assoc}, repeat {rw myfld.mul_comm _ u}, repeat {rw <- myfld.mul_assoc}, 
  repeat {rw mul_negate_alt f u _}, 
  rw myfld.add_assoc (fourth_power f _) (u .* _) _, rw myfld.add_comm (fourth_power f _) (u .* _), 
  repeat {rw <- myfld.add_assoc}, 
  rw myfld.add_comm (u .* d) _, repeat {rw myfld.add_assoc}, 
  rw myfld.add_comm _ (u .* d), repeat {rw <- myfld.add_assoc}, 
  rw myfld.add_comm (u .* (.- ((two f) .* _))) _, repeat {rw myfld.add_assoc}, 
  rw myfld.add_comm _ (u .* (.- ((two f) .* _))), repeat {rw myfld.add_assoc}, 
  repeat {rw <- distrib_simp_alt f u _ _}, 
  rw quartic_reduce_linear_helper, repeat {rw <- myfld.add_assoc}, 
  apply clear_term, 

  /- constant term...-/ 
  rw quartic_reduce_constant_helper, 
end

/- This is the solution to a cubic described under "alternative methods" on Wikipedia.-/ 
lemma depressed_quartic_to_quadratic_product (f : Type) [myfld f] (c d e p q s x : f)
                                              (p_ne_zero : p ≠ myfld.zero) : 
  (c .+ (square f p)) = (s .+ q) /\ 
  (d .* (myfld.reciprocal p p_ne_zero) = s .+ (.- q)) /\ 
  (e = s .* q)
  -> 
  depressed_quartic_subst f c d e x = 
      (quadratic_subst f x myfld.one p q) .* (quadratic_subst f x myfld.one (.- p) s) := 
begin 
  intros h, cases h with h1 h2, cases h2 with h2 h3, 
  unfold quadratic_subst, rw one_mul_simp, 
  repeat {rw distrib_simp}, repeat {rw distrib_simp_alt}, 
  repeat {rw myfld.mul_assoc}, repeat {rw mul_negate_alt_simp}, repeat {rw mul_negate}, 
  repeat {rw myfld.mul_comm (x .* x) _}, 
  repeat {rw myfld.mul_comm x p}, repeat {rw myfld.mul_comm x s}, 
  rw myfld.mul_comm (p .* x) s, rw myfld.mul_comm (p .* x) p, 
  repeat {rw myfld.mul_assoc _ _ x}, repeat {rw <- myfld.mul_assoc _ x x}, 
  rw myfld.add_comm (.- ((p .* x) .* (x .* x))), 
  repeat {rw <- myfld.add_assoc}, rw myfld.add_assoc (.- ((p .* x) .* _)) _ _, 
  rw myfld.add_comm (.- ((p .* x) .* _)) _, rw myfld.add_negate _, rw simp_zero, 
  have clear_term : ∀ (a b x : f), a = b -> (x .+ a) = (x .+ b), 
    intros a b x h, rw h, 
  unfold depressed_quartic_subst, unfold fourth_power, repeat {rw <- myfld.mul_assoc}, 
  apply clear_term, 
  rw h3, clear h3, repeat {rw myfld.add_assoc}, rw myfld.mul_comm s q, 
  repeat {rw myfld.add_comm _ (q .* s) }, 
  apply clear_term, 
  rw myfld.add_comm _ (.- (q .* (p .* x))), 
  rw myfld.add_comm _ (s .* (p .* x)), 
  rw <- mul_negate f _ (p .* x), 
  repeat {rw <- myfld.add_assoc}, 
  rw myfld.add_assoc (_ .* (p .* x)) (_ .* (p .* x)) _, 
  rw <- distrib_simp f _ _ (p .* x), 
  rw myfld.mul_assoc _ p x, 
  have h3 : (d .* (myfld.reciprocal p p_ne_zero)) .* p = (s .+ (.- q)) .* p,
    rw h2, clear h2, 
  rw <- myfld.mul_assoc at h3, rw myfld.mul_comm (myfld.reciprocal _ _) p at h3, rw myfld.mul_reciprocal p _ at h3, 
  clear p_ne_zero, rw simp_mul_one at h3, rw myfld.add_comm _ (d .* x), rw h3, clear h3, 
  rw myfld.add_comm s (.- q), 
  apply clear_term, clear clear_term, 
  rw myfld.mul_assoc p p _, rw <- mul_negate f _ (x .* x), 
  repeat {rw <- distrib_simp f _ _ (x .* x) }, 
  have h2 : (c .+ (square f p)) .+ (.- (square f p)) = (s .+ q) .+ (.- (square f p)) , 
    rw h1, clear h1, 
  rw <- myfld.add_assoc at h2, rw myfld.add_negate at h2, rw zero_simp at h2, 
  rw h2, clear h2, unfold square, 
  rw myfld.add_comm (.- _) _, repeat {rw myfld.add_assoc}, 
end 

lemma simultaneous_solution_helper (f : Type) [myfld f] [fld_not_char_two f] (c d e p q s : f) (p_ne_zero : p ≠ myfld.zero) : 
  cubic_subst f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) (square f p)
  = myfld.zero -> 
  e = ((myfld.reciprocal ((two f) .* (two f)) (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two)) .* ((fourth_power f p) .+ (((two f) .* (c .* (square f p))) .+ (square f c)))) .+ ((myfld.reciprocal ((two f) .* (two f)) (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two)) .* (.- (square f (d .* (myfld.reciprocal p p_ne_zero))))) := 
begin 
  intros h_tmp, unfold cubic_subst at h_tmp, rw one_mul at h_tmp, 
      rw mul_both_sides f _ _ (square f p) (square_ne_zero f p p_ne_zero), 
      rw mul_negate_alt_simp, 
      repeat {rw distrib_simp f _ _ (square f p) }, rw <- mul_two_squares f d _, rw mul_negate, 
      repeat {rw <- myfld.mul_assoc}, rw mul_two_squares f _ p, rw myfld.mul_comm _ p, rw myfld.mul_reciprocal p _, 
      have squ_one : ∀ (x : f), x .* (square f myfld.one) = x, 
        intros x, unfold square, rw simp_mul_one, rw simp_mul_one, 
      rw squ_one, clear squ_one, 
      rw myfld.mul_comm (_ .+ _) (square f p), rw distrib_simp_alt f (square f p), 
      rw mul_both_sides f _ _ (four f) (four_ne_zero f), unfold four, rw two_plus_two, 
      repeat {rw distrib_simp f _ _ ((two f) .* (two f)) }, 
      repeat {rw myfld.mul_comm (myfld.reciprocal ((two f) .* (two f)) _) _}, 
      rw mul_negate, 
      repeat {rw <- myfld.mul_assoc _ (myfld.reciprocal (_ .* _) _) (_ .* _) }, 
      repeat {rw myfld.mul_comm (myfld.reciprocal (_ .* _) _) (_ .* _) }, 
      repeat {rw myfld.mul_reciprocal _ _}, repeat {rw simp_mul_one f _}, 
      have sixth_power : ((square f p) .* (fourth_power f p)) = (cubed f (square f p)), 
        unfold square, unfold cubed, unfold fourth_power, repeat {rw myfld.mul_assoc}, 
      rw sixth_power, clear sixth_power, 
      rw carry_term_across_alt, 
      symmetry, rw myfld.mul_comm (square f p) _, 
      rw distrib_simp, rw distrib_simp at h_tmp, unfold four at h_tmp, rw two_plus_two at h_tmp, 
      repeat {rw myfld.add_assoc}, repeat {rw myfld.add_assoc at h_tmp}, 
      rw myfld.add_comm _ (.- (square f d)), rw myfld.add_comm _ (.- (square f d)) at h_tmp, 
      repeat {rw myfld.add_assoc}, repeat {rw myfld.add_assoc at h_tmp}, 
      unfold square, unfold cubed, unfold square at h_tmp, unfold cubed at h_tmp, 
      rw myfld.mul_comm ((two f) .* (two f)) e at h_tmp, 
      rw <- myfld.mul_assoc _ (two f) (two f), 
      rw <- myfld.mul_assoc e (p .* p) _, rw myfld.mul_comm (p .* p) ((two f) .* (two f)), 
      repeat {rw myfld.mul_assoc}, repeat {rw myfld.mul_assoc at h_tmp}, 
      rw mul_negate at h_tmp, rw mul_negate at h_tmp, 
      exact h_tmp, 
end 

lemma simultaneous_solution (f : Type) [myfld f] [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
     (c d e p q s : f) (p_ne_zero : p ≠ myfld.zero)
     (int_quantity_ne_zero : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero) : 
  p = sqroot 
      (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero) -> 
  s = ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f p) .+ (d .* (myfld.reciprocal p p_ne_zero))))) -> 
  q = ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f p) .+ ((.- d) .* (myfld.reciprocal p p_ne_zero)))))
  -> 
  (c .+ (square f p)) = (s .+ q) /\ 
  (d .* (myfld.reciprocal p p_ne_zero) = s .+ (.- q)) /\ 
  (e = s .* q) := 
begin 
  intros hp hs hq, split, 
    rw hs, rw hq, rw mul_negate, rw <- distrib_simp_alt, 
    rw myfld.add_assoc _ _ (.- _), rw myfld.add_comm _ (.- _), 
    rw myfld.add_assoc _ (.- _) _, rw myfld.add_assoc _ _ (d .* (myfld.reciprocal p p_ne_zero)), 
    rw <- myfld.add_assoc _ _ (.- _), 
    rw myfld.add_negate, rw zero_simp, 
    rw two_x_div_two, 

  split, 
    rw hs, rw hq, rw mul_negate_alt, rw <- distrib_simp_alt, rw mul_negate, repeat {rw add_negate}, rw double_negative, 
    rw myfld.add_assoc (.- _) (.- _) _, rw <- add_negate, 
    rw myfld.add_assoc c _ _, rw myfld.add_comm (c .+ _) _, 
    rw myfld.add_assoc _ (.- (c .+ (square f p))) _, 
    rw <- myfld.add_assoc _ _ (.- (c .+ (square f p))), rw myfld.add_negate, rw zero_simp, 
    rw two_x_div_two, 

    rw hs, rw hq, clear hs, clear hq, 
    rw mul_negate, rw myfld.mul_assoc _ (myfld.reciprocal _ _) _, rw myfld.mul_comm _ (myfld.reciprocal _ _), 
    rw myfld.mul_assoc (myfld.reciprocal _ _) (myfld.reciprocal _ _) _, 
    rw <- myfld.mul_assoc _ (_ .+ _) (_ .+ _), rw mul_two_reciprocals, 
    repeat {rw myfld.add_assoc c _ _}, rw difference_of_squares, 
    have tmp : (square f (c .+ (square f p))) = 
                (fourth_power f p) .+ (((two f) .* (c .* (square f p))) .+ (square f c)) , 
      unfold square, unfold two, repeat {rw distrib_simp}, repeat {rw distrib_simp_alt}, unfold fourth_power, 
      rw one_mul_simp, repeat {rw myfld.mul_assoc}, repeat {rw myfld.add_assoc}, 
      rw myfld.add_comm _ (((p .* p) .* p) .* p), rw myfld.add_comm (c .* c) _, 
      rw <- myfld.add_assoc _ (c .* c) _, rw myfld.add_comm (c .* c) _, 
      rw myfld.mul_comm (p .* p) c, repeat {rw myfld.mul_assoc}, repeat {rw myfld.add_assoc}, 
    rw tmp, clear tmp, 
    rw only_one_reciprocal f ((two f) .* (two f)) _ (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two), 

    apply simultaneous_solution_helper f c d e p q s p_ne_zero, 

    rw hp, repeat {rw sqrt_squared}, 

    exact cubic_formula_a_correct f myfld.one _ _ _ (myfld.zero_distinct_one) int_quantity_ne_zero, 
end 

lemma depressed_quartic_to_quadratic_product_solved (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] (c d e x : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)

        : 
  (depressed_quartic_subst f c d e x) = 
  ((quadratic_subst f x myfld.one (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ ((.- d) .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b))))))) .* (quadratic_subst f x myfld.one (.- (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ (d .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b))))))))
  := 
begin
  apply depressed_quartic_to_quadratic_product, 
  apply simultaneous_solution, 
    refl, 
    refl, 
    refl, 
end

lemma depressed_quartic_to_linear_factorization (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] (c d e x : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        :  (depressed_quartic_subst f c d e x) = 
  (x .+ .- (quadratic_formula f myfld.one 
                            (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ ((.- d) .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b)))))) myfld.zero_distinct_one)) .* (x .+ .- (quadratic_formula_alt f myfld.one (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ ((.- d) .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b)))))) myfld.zero_distinct_one)) .* (x .+ .- (quadratic_formula f myfld.one (.- (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ ((d) .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b)))))) myfld.zero_distinct_one)) .* (x .+ .- (quadratic_formula_alt f myfld.one (.- (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ ((d) .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b)))))) myfld.zero_distinct_one)) 
  :=
begin
  rw depressed_quartic_to_quadratic_product_solved f c d e x int_quantity_ne_zero_a int_quantity_ne_zero_b,
  rw <- quadratic_factorize, rw <- quadratic_factorize,
  repeat {rw myfld.mul_assoc},
end

/- We now need to devote a bit of space to some fairly trivial boilerplate to make the solution to 
      a product of quadratics explicit.-/ 
lemma quadratic_product_solution (f : Type) [myfld f] [fld_not_char_two f] [fld_with_sqrt f] (b1 b2 c1 c2 x : f) : 
    ((x = quadratic_formula f myfld.one b1 c1 myfld.zero_distinct_one) \/ (x = quadratic_formula_alt f myfld.one b1 c1 myfld.zero_distinct_one) \/ (x = quadratic_formula f myfld.one b2 c2 myfld.zero_distinct_one) \/ (x = quadratic_formula_alt f myfld.one b2 c2 myfld.zero_distinct_one)) -> 
  (quadratic_subst f x myfld.one b1 c1) .* (quadratic_subst f x myfld.one b2 c2) = myfld.zero := 
begin 
  intros h, cases h, 
    have h1 : (quadratic_subst f x myfld.one b1 c1) = myfld.zero, 
      rw h, exact quadratic_formula_works f myfld.one b1 c1 myfld.zero_distinct_one, 
    rw h1, exact mul_zero f _, 
  cases h, 
    have h1 : (quadratic_subst f x myfld.one b1 c1) = myfld.zero, 
      rw h, exact quadratic_formula_alt_works f myfld.one b1 c1 myfld.zero_distinct_one, 
    rw h1, exact mul_zero f _, 
  cases h, 
    have h1 : (quadratic_subst f x myfld.one b2 c2) = myfld.zero, 
      rw h, exact quadratic_formula_works f myfld.one b2 c2 myfld.zero_distinct_one, 
    rw h1, exact zero_mul f _, 
    have h1 : (quadratic_subst f x myfld.one b2 c2) = myfld.zero, 
      rw h, exact quadratic_formula_alt_works f myfld.one b2 c2 myfld.zero_distinct_one, 
    rw h1, exact zero_mul f _, 
end 

lemma quadratic_product_solution_unique (f : Type) [myfld f] [fld_not_char_two f] [fld_with_sqrt f] (b1 b2 c1 c2 x : f) : 
     (x ≠ quadratic_formula f myfld.one b1 c1 myfld.zero_distinct_one) -> 
     (x ≠ quadratic_formula_alt f myfld.one b1 c1 myfld.zero_distinct_one) -> 
     (x ≠ quadratic_formula f myfld.one b2 c2 myfld.zero_distinct_one) -> 
     (x ≠ quadratic_formula_alt f myfld.one b2 c2 myfld.zero_distinct_one) -> 
  (quadratic_subst f x myfld.one b1 c1) .* (quadratic_subst f x myfld.one b2 c2) ≠ myfld.zero := 
begin 
  intros h1 h2 h3 h4, 
  have left_ne_zero : (quadratic_subst f x myfld.one b1 c1) ≠ myfld.zero, 
    apply quadratic_solution_unique f myfld.one b1 c1 _ myfld.zero_distinct_one, 
    split, cc, cc, 
  have right_ne_zero : (quadratic_subst f x myfld.one b2 c2) ≠ myfld.zero, 
    apply quadratic_solution_unique f myfld.one b2 c2 _ myfld.zero_distinct_one, 
    split, cc, cc, 
  exact mul_nonzero f _ _ left_ne_zero right_ne_zero, 
end 

def depressed_quartic_solution_a (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
            (c d e: f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        : f := 
              (quadratic_formula f myfld.one (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ ((.- d) .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b)))))) myfld.zero_distinct_one)

lemma depressed_quartic_solution_a_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] (c d e : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        : depressed_quartic_subst f c d e (depressed_quartic_solution_a f c d e int_quantity_ne_zero_a int_quantity_ne_zero_b)
                                    = myfld.zero := 
begin 
  rw depressed_quartic_to_quadratic_product_solved, apply quadratic_product_solution, left, unfold depressed_quartic_solution_a, 
  exact int_quantity_ne_zero_b, 
end 

def depressed_quartic_solution_b (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
            (c d e : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        : f := 
              (quadratic_formula_alt f myfld.one (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ ((.- d) .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b)))))) myfld.zero_distinct_one)

lemma depressed_quartic_solution_b_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] (c d e : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        : depressed_quartic_subst f c d e (depressed_quartic_solution_b f c d e int_quantity_ne_zero_a int_quantity_ne_zero_b)
                                    = myfld.zero := 
begin 
  rw depressed_quartic_to_quadratic_product_solved, apply quadratic_product_solution, right, left, 
  unfold depressed_quartic_solution_b, 
  exact int_quantity_ne_zero_b, 
end 

def depressed_quartic_solution_c (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
            (c d e : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        : f := 
              (quadratic_formula f myfld.one (.- (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ (d .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b)))))) myfld.zero_distinct_one)

lemma depressed_quartic_solution_c_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] (c d e : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        : depressed_quartic_subst f c d e (depressed_quartic_solution_c f c d e int_quantity_ne_zero_a int_quantity_ne_zero_b)
                                    = myfld.zero := 
begin 
  rw depressed_quartic_to_quadratic_product_solved, apply quadratic_product_solution, right, right, left, 
  unfold depressed_quartic_solution_c, 
  exact int_quantity_ne_zero_b, 
end 

def depressed_quartic_solution_d (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
            (c d e : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        : f := 
              (quadratic_formula_alt f myfld.one (.- (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (c .+ ((square f (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a))) .+ (d .* (myfld.reciprocal (sqroot (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a)) (sqrt_ne_zero f (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) int_quantity_ne_zero_b)))))) myfld.zero_distinct_one)

lemma depressed_quartic_solution_d_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] (c d e : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        : depressed_quartic_subst f c d e (depressed_quartic_solution_d f c d e int_quantity_ne_zero_a int_quantity_ne_zero_b)
                                    = myfld.zero := 
begin 
  rw depressed_quartic_to_quadratic_product_solved, apply quadratic_product_solution, right, right, right, 
  unfold depressed_quartic_solution_d, 
  exact int_quantity_ne_zero_b, 
end 


lemma depressed_quartic_solution_uniqueness (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] (c d e x : f)
            (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f c) .+ (.- ((four f) .* e))))) .+ (.- (square f ((two f) .* c)))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* c) ((square f c) .+ (.- ((four f) .* e))) (.- (square f d)) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
        : (x ≠ (depressed_quartic_solution_a f c d e int_quantity_ne_zero_a int_quantity_ne_zero_b)) -> 
          (x ≠ (depressed_quartic_solution_b f c d e int_quantity_ne_zero_a int_quantity_ne_zero_b)) -> 
          (x ≠ (depressed_quartic_solution_c f c d e int_quantity_ne_zero_a int_quantity_ne_zero_b)) -> 
          (x ≠ (depressed_quartic_solution_d f c d e int_quantity_ne_zero_a int_quantity_ne_zero_b)) -> 
        (depressed_quartic_subst f c d e x ≠ myfld.zero) := 
begin 
  intros ha hb hc hd, rw depressed_quartic_to_quadratic_product_solved, apply quadratic_product_solution_unique, 

  unfold depressed_quartic_solution_a at ha, exact ha, 
  unfold depressed_quartic_solution_b at hb, exact hb, 
  unfold depressed_quartic_solution_c at hc, exact hc, 
  unfold depressed_quartic_solution_d at hd, exact hd, 
  exact int_quantity_ne_zero_b, 
end

/- This is the end of the actual interesting content in this file.  The remainder
    is just an enormous amount of boilerplate to make it explicit that the
    four solutions to a depressed quartic imply four solutions to a full quartic.
    This should be obvious from all of the above to any thinking reader,
    but it still seemed incomplete to not make it explicit. -/

def quartic_formula_int_a (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (b c d e : f)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f b c))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f b c)) ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))) (.- (square f (depressed_quartic_linear_coeff f b c d))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : f := ((depressed_quartic_solution_a f (depressed_quartic_squ_coeff f b c) (depressed_quartic_linear_coeff f b c d) (depressed_quartic_constant f b c d e) int_quantity_ne_zero_a int_quantity_ne_zero_b) .+ (.- (b .* (myfld.reciprocal (four f) (four_ne_zero f)))))

lemma quartic_formula_int_a_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (b c d e : f)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f b c))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f b c)) ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))) (.- (square f (depressed_quartic_linear_coeff f b c d))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : (quartic_expression f (quartic_formula_int_a f b c d e int_quantity_ne_zero_a int_quantity_ne_zero_b) myfld.one b c d e) = myfld.zero := 
begin 
  rw reduce_quartic_to_depressed f b c d e (quartic_formula_int_a f b c d e int_quantity_ne_zero_a int_quantity_ne_zero_b) (depressed_quartic_solution_a f (depressed_quartic_squ_coeff f b c) (depressed_quartic_linear_coeff f b c d) (depressed_quartic_constant f b c d e) int_quantity_ne_zero_a int_quantity_ne_zero_b) _, 
  apply depressed_quartic_solution_a_works, 
  unfold quartic_formula_int_a, 
end 

def quartic_formula_a (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (a b c d e : f) (a_ne_zero : a ≠ myfld.zero)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero))))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))) (.- (square f (depressed_quartic_linear_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero))))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : f := (quartic_formula_int_a f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)) int_quantity_ne_zero_a int_quantity_ne_zero_b)

lemma quartic_formula_a_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (a b c d e : f) (a_ne_zero : a ≠ myfld.zero)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero))))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))) (.- (square f (depressed_quartic_linear_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero))))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : quartic_expression f 
                            (quartic_formula_a f a b c d e a_ne_zero int_quantity_ne_zero_a int_quantity_ne_zero_b)
                            a b c d e 
          = myfld.zero := 
begin 
  rw remove_fourth_power_coefficient, unfold quartic_formula_a, 
  exact quartic_formula_int_a_works f _ _ _ _ int_quantity_ne_zero_a int_quantity_ne_zero_b, 
end

def quartic_formula_int_b (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (b c d e : f)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f b c))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f b c)) ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))) (.- (square f (depressed_quartic_linear_coeff f b c d))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : f := ((depressed_quartic_solution_b f (depressed_quartic_squ_coeff f b c) (depressed_quartic_linear_coeff f b c d) (depressed_quartic_constant f b c d e) int_quantity_ne_zero_a int_quantity_ne_zero_b) .+ (.- (b .* (myfld.reciprocal (four f) (four_ne_zero f)))))

lemma quartic_formula_int_b_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (b c d e : f)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f b c))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f b c)) ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))) (.- (square f (depressed_quartic_linear_coeff f b c d))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : (quartic_expression f (quartic_formula_int_b f b c d e int_quantity_ne_zero_a int_quantity_ne_zero_b) myfld.one b c d e) = myfld.zero := 
begin 
  rw reduce_quartic_to_depressed f b c d e (quartic_formula_int_b f b c d e int_quantity_ne_zero_a int_quantity_ne_zero_b) (depressed_quartic_solution_b f (depressed_quartic_squ_coeff f b c) (depressed_quartic_linear_coeff f b c d) (depressed_quartic_constant f b c d e) int_quantity_ne_zero_a int_quantity_ne_zero_b) _, 
  apply depressed_quartic_solution_b_works, 
  unfold quartic_formula_int_b,
end

def quartic_formula_b (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (a b c d e : f) (a_ne_zero : a ≠ myfld.zero)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero))))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))) (.- (square f (depressed_quartic_linear_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero))))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : f := (quartic_formula_int_b f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)) int_quantity_ne_zero_a int_quantity_ne_zero_b)

lemma quartic_formula_b_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (a b c d e : f) (a_ne_zero : a ≠ myfld.zero)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero))))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))) (.- (square f (depressed_quartic_linear_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero))))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : quartic_expression f 
                            (quartic_formula_b f a b c d e a_ne_zero int_quantity_ne_zero_a int_quantity_ne_zero_b)
                            a b c d e 
          = myfld.zero := 
begin 
  rw remove_fourth_power_coefficient, unfold quartic_formula_b, 
  exact quartic_formula_int_b_works f _ _ _ _ int_quantity_ne_zero_a int_quantity_ne_zero_b,
end

def quartic_formula_int_c (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (b c d e : f)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f b c))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f b c)) ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))) (.- (square f (depressed_quartic_linear_coeff f b c d))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : f := ((depressed_quartic_solution_c f (depressed_quartic_squ_coeff f b c) (depressed_quartic_linear_coeff f b c d) (depressed_quartic_constant f b c d e) int_quantity_ne_zero_a int_quantity_ne_zero_b) .+ (.- (b .* (myfld.reciprocal (four f) (four_ne_zero f)))))

lemma quartic_formula_int_c_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (b c d e : f)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f b c))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f b c)) ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))) (.- (square f (depressed_quartic_linear_coeff f b c d))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : (quartic_expression f (quartic_formula_int_c f b c d e int_quantity_ne_zero_a int_quantity_ne_zero_b) myfld.one b c d e) = myfld.zero := 
begin 
  rw reduce_quartic_to_depressed f b c d e (quartic_formula_int_c f b c d e int_quantity_ne_zero_a int_quantity_ne_zero_b) (depressed_quartic_solution_c f (depressed_quartic_squ_coeff f b c) (depressed_quartic_linear_coeff f b c d) (depressed_quartic_constant f b c d e) int_quantity_ne_zero_a int_quantity_ne_zero_b) _, 
  apply depressed_quartic_solution_c_works, 
  unfold quartic_formula_int_c,
end

def quartic_formula_c (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (a b c d e : f) (a_ne_zero : a ≠ myfld.zero)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero))))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))) (.- (square f (depressed_quartic_linear_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero))))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : f := (quartic_formula_int_c f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)) int_quantity_ne_zero_a int_quantity_ne_zero_b)

lemma quartic_formula_c_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (a b c d e : f) (a_ne_zero : a ≠ myfld.zero)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero))))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))) (.- (square f (depressed_quartic_linear_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero))))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : quartic_expression f 
                            (quartic_formula_c f a b c d e a_ne_zero int_quantity_ne_zero_a int_quantity_ne_zero_b)
                            a b c d e 
          = myfld.zero := 
begin 
  rw remove_fourth_power_coefficient, unfold quartic_formula_c, 
  exact quartic_formula_int_c_works f _ _ _ _ int_quantity_ne_zero_a int_quantity_ne_zero_b,
end

def quartic_formula_int_d (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (b c d e : f)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f b c))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f b c)) ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))) (.- (square f (depressed_quartic_linear_coeff f b c d))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : f := ((depressed_quartic_solution_d f (depressed_quartic_squ_coeff f b c) (depressed_quartic_linear_coeff f b c d) (depressed_quartic_constant f b c d e) int_quantity_ne_zero_a int_quantity_ne_zero_b) .+ (.- (b .* (myfld.reciprocal (four f) (four_ne_zero f)))))

lemma quartic_formula_int_d_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (b c d e : f)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f b c))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f b c)) ((square f (depressed_quartic_squ_coeff f b c)) .+ (.- ((four f) .* (depressed_quartic_constant f b c d e)))) (.- (square f (depressed_quartic_linear_coeff f b c d))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : (quartic_expression f (quartic_formula_int_d f b c d e int_quantity_ne_zero_a int_quantity_ne_zero_b) myfld.one b c d e) = myfld.zero := 
begin 
  rw reduce_quartic_to_depressed f b c d e (quartic_formula_int_d f b c d e int_quantity_ne_zero_a int_quantity_ne_zero_b) (depressed_quartic_solution_d f (depressed_quartic_squ_coeff f b c) (depressed_quartic_linear_coeff f b c d) (depressed_quartic_constant f b c d e) int_quantity_ne_zero_a int_quantity_ne_zero_b) _, 
  apply depressed_quartic_solution_d_works, 
  unfold quartic_formula_int_d,
end

def quartic_formula_d (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (a b c d e : f) (a_ne_zero : a ≠ myfld.zero)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero))))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))) (.- (square f (depressed_quartic_linear_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero))))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : f := (quartic_formula_int_d f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)) int_quantity_ne_zero_a int_quantity_ne_zero_b)

lemma quartic_formula_d_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
       (a b c d e : f) (a_ne_zero : a ≠ myfld.zero)
       (int_quantity_ne_zero_a : (((three f) .* (myfld.one .* ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))))) .+ (.- (square f ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero))))))) ≠ myfld.zero)
            (int_quantity_ne_zero_b : (cubic_formula_a f myfld.one ((two f) .* (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) ((square f (depressed_quartic_squ_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((four f) .* (depressed_quartic_constant f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) (e .* (myfld.reciprocal a a_ne_zero)))))) (.- (square f (depressed_quartic_linear_coeff f (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero))))) myfld.zero_distinct_one int_quantity_ne_zero_a) ≠ myfld.zero)
       : quartic_expression f 
                            (quartic_formula_d f a b c d e a_ne_zero int_quantity_ne_zero_a int_quantity_ne_zero_b)
                            a b c d e 
          = myfld.zero := 
begin 
  rw remove_fourth_power_coefficient, unfold quartic_formula_d, 
  exact quartic_formula_int_d_works f _ _ _ _ int_quantity_ne_zero_a int_quantity_ne_zero_b,
end