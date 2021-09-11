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

def depressed_cubic_subst (f : Type) [myfld f] (c d x : f) : f := 
  (cubed f x) .+ ((c .* x) .+ d)

lemma depressed_cubic_solution_two_vars (f : Type) [myfld f] (x c d s t : f) : 
    (x = myfld.add s (myfld.negate t)) /\ 
    c = (myfld.mul (three f) (myfld.mul s t)) /\ 
    d = (myfld.add (cubed f s) (myfld.negate (cubed f t))) -> 
        (myfld.add (cubed f x) (myfld.mul c x) = d) :=
begin
  intros h, cases h with hx h, cases h with ha hb,
  rw hx, rw ha, rw hb, rw multiply_out_cubed f s (myfld.negate t),
  rw distrib_simp_alt f _ _ _,
  repeat {rw <- mul_negate_alt f _ _}, repeat {rw mul_negate f _ _}, repeat {rw <- mul_negate_alt f _ _},
  rw double_negative f _,
  have tmp : (cubed f (myfld.negate t)) = myfld.negate (cubed f t),
    unfold cubed, repeat {rw mul_negate_alt_simp f _ _}, repeat {rw mul_negate f _ _}, rw double_negative f _,
    rw mul_negate_alt_simp f _ _,
  rw tmp, clear tmp,
  rw <- myfld.mul_assoc _ (s .* t) s, rw myfld.mul_comm (s .* t) s,
  unfold square, repeat {rw myfld.mul_assoc},
  rw myfld.add_assoc _ (three f) .* s .* s .* t _, rw myfld.add_comm _ (three f) .* s .* s .* t,
  repeat {rw <- myfld.add_assoc},
  rw myfld.add_assoc _ (.- ((three f) .* s .* s .* t)) _, rw myfld.add_comm _ (.- ((three f) .* s .* s .* t)),
  repeat {rw myfld.add_assoc}, rw myfld.add_negate, rw simp_zero,
  rw myfld.add_comm _ (.- ((three f) .* s .* t .* t)),
  rw myfld.add_comm _ (three f) .* s .* t .* t,
  repeat {rw myfld.add_assoc}, rw myfld.add_comm (.- ((three f) .* s .* t .* t)) _,
  rw myfld.add_negate, rw simp_zero,
end

lemma depressed_cubic_simultaneous_solution (f : Type) [myfld f] 
    [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f]
 (c d s t : f) (c_ne_zero : c ≠ myfld.zero) (s_ne_zero : s ≠ myfld.zero):
    (s = fld_with_cube_root.cubrt 
        (quadratic_formula f myfld.one (.- d) 
                (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one))
    -> (t = myfld.mul c (myfld.reciprocal ((three f) .* s) (mul_nonzero f (three f) s fld_not_char_three.not_char_three
                                                                            s_ne_zero))) ->
    ((c = myfld.mul (three f) (myfld.mul s t)) /\ (d = myfld.add (cubed f s) (myfld.negate (cubed f t)))) :=
begin
  intros hs ht,
  have hs_tmp : (cubed f s) = (quadratic_formula f myfld.one (.- d) (.- (cubed f c) .* 
                                    (myfld.reciprocal (twenty_seven f) _)) myfld.zero_distinct_one),
    rw hs, rw cubrt_cubed, clear hs, rename hs_tmp hs,
  split,
    rw ht, rw myfld.mul_assoc, rw myfld.mul_comm c _, rw myfld.mul_assoc, rw myfld.mul_reciprocal, rw one_mul_simp,

    have ht_tmp : (cubed f t) = 
                          (cubed f c) .* 
                          (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f)) .* 
                          (myfld.reciprocal (cubed f s) (cube_nonzero f s s_ne_zero)),
      rw ht, rw cube_of_product, rw cube_of_reciprocal,
      rw reciprocal_rewrite f _ _ (cube_of_product f _ _), rw split_reciprocal f,
      rw reciprocal_rewrite f _ _ (three_cubed f) _,
      rw only_one_reciprocal f (twenty_seven f) _ (twenty_seven_ne_zero f),
      rw only_one_reciprocal f (cubed f s) _ (cube_nonzero f s s_ne_zero),
      rw myfld.mul_assoc,
    clear ht, rename ht_tmp ht, rw ht,
    rw mul_both_sides f _ _ (cubed f s) (cube_nonzero f s s_ne_zero),
    rw carry_term_across_alt, rw distrib_simp, symmetry,
    rw <- mul_negate f d (cubed f s), rw mul_negate, repeat {rw <- myfld.mul_assoc},
    rw myfld.mul_comm (myfld.reciprocal _ _) (cubed f _), rw myfld.mul_reciprocal, rw simp_mul_one,
    rw <- myfld.add_assoc, rw myfld.add_comm _ (.-d .* _),
    have tmp : quadratic_subst f (cubed f s) myfld.one (.- d) (.- ((cubed f c) .* (myfld.reciprocal (twenty_seven f) _)))
                  = myfld.zero,
      rw hs, rw only_one_reciprocal f (twenty_seven f) _ (twenty_seven_ne_zero f),
      rw mul_negate,
      exact quadratic_formula_works f myfld.one (.- d) (.- ((cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f)))) myfld.zero_distinct_one,
    unfold quadratic_subst at tmp, rw one_mul_simp at tmp, exact tmp,
end

lemma cardano_den_ne_zero (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d : f) (c_ne_zero : c ≠ myfld.zero) 
      : (quadratic_formula f myfld.one (d) (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one ≠ myfld.zero)
      :=
begin
  unfold quadratic_formula, apply mul_nonzero,
  intros h, rw carry_term_across at h, rw simp_zero at h,
  have tmp : ∀ (a b : f), (.- a = .- b) <-> (a = b),
    intros a b, split, intros h, have tmp_tmp : .- .- a = .- .- b, rw h,
    repeat {rw double_negative at tmp_tmp}, exact tmp_tmp,
    intros h, rw h,
  rw tmp at h, clear tmp,
  have h_tmp : d .* d = sqroot (d .* d .+ .- ((four f) .* (myfld.one .* ( .- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f)))))) .* sqroot (d .* d .+ .- ((four f) .* (myfld.one .* ( .- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f)))))),
    rw <- h,
  clear h, rename h_tmp h,
  rw fld_with_sqrt.sqrt_mul_sqrt at h,
  have tmp : ∀ (a b : f), (a = a .+ b) <-> (b = myfld.zero), intros a b, split,
    intros h, have tmp_tmp : (.- a) .+ a = (.- a) .+ (a .+ b), rw <- h,
    rw myfld.add_assoc at tmp_tmp, rw myfld.add_comm (.- a) a at tmp_tmp,
    rw myfld.add_negate a at tmp_tmp, rw simp_zero at tmp_tmp, symmetry, exact tmp_tmp,
    intros h, rw h, rw zero_simp,
  rw tmp at h, clear tmp,
  rw one_mul_simp at h, repeat {rw mul_negate at h}, rw mul_negate_alt_simp at h,
  rw double_negative at h,
  exact (mul_nonzero f (four f) (_ .* _) (four_ne_zero f) (mul_nonzero f _ _ (cube_nonzero f c c_ne_zero) (reciprocal_ne_zero f _ _))) h,
  exact reciprocal_ne_zero f _ _,
end

def cardano_formula_new (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
    (c d : f) (c_ne_zero : c ≠ myfld.zero) (cubrt_func : f -> f)
      (cubrt_func_nonzero : ∀ (x : f), x ≠ myfld.zero -> (cubrt_func x ≠ myfld.zero))
      (cubrt_func_correct : ∀ (x : f), (cubed f (cubrt_func x)) = x) : f := 
  (fld_with_cube_root.cubrt 
        (quadratic_formula f myfld.one d 
                (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one))
    .+ .- (myfld.mul c (myfld.reciprocal ((three f) .* (fld_with_cube_root.cubrt 
        (quadratic_formula f myfld.one d 
                (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one))) (mul_nonzero f (three f) (fld_with_cube_root.cubrt 
        (quadratic_formula f myfld.one d 
                (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one)) fld_not_char_three.not_char_three
                                                                            (cubrt_nonzero f (quadratic_formula f myfld.one (d) (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one) (cardano_den_ne_zero f c d c_ne_zero)))))

def cardano_formula_a_new (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f]
    (c d : f) (c_ne_zero : c ≠ myfld.zero) : f :=
    cardano_formula_new f c d c_ne_zero fld_with_cube_root.cubrt (cubrt_nonzero f) (cubrt_cubed f)

def cardano_formula_b_new (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f]
    (c d : f) (c_ne_zero : c ≠ myfld.zero) : f :=
    cardano_formula_new f c d c_ne_zero (alt_cubrt_a f) (alt_cubrt_a_nonzero f) (alt_cubrt_a_correct f)

def cardano_formula_c_new (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f]
    (c d : f) (c_ne_zero : c ≠ myfld.zero) : f :=
    cardano_formula_new f c d c_ne_zero (alt_cubrt_b f) (alt_cubrt_b_nonzero f) (alt_cubrt_b_correct f)

lemma cardano_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d : f) (c_ne_zero : c ≠ myfld.zero) (cubrt_func : f -> f)
      (cubrt_func_nonzero : ∀ (x : f), x ≠ myfld.zero -> (cubrt_func x ≠ myfld.zero))
      (cubrt_func_correct : ∀ (x : f), (cubed f (cubrt_func x)) = x) :
      depressed_cubic_subst f c d (cardano_formula_new f c d c_ne_zero cubrt_func cubrt_func_nonzero cubrt_func_correct) 
            = myfld.zero :=
begin
  have clear_term : ∀ (a b x : f), a = b -> (x .+ a) = (x .+ b), 
    intros a b x h, rw h, 
  unfold depressed_cubic_subst, rw myfld.add_assoc, rw carry_term_across,
  rw simp_zero,
  apply depressed_cubic_solution_two_vars f (cardano_formula_new f c d c_ne_zero cubrt_func cubrt_func_nonzero cubrt_func_correct)
                                               c (.- d) (fld_with_cube_root.cubrt 
        (quadratic_formula f myfld.one (d) 
                (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one)) ((myfld.mul c (myfld.reciprocal ((three f) .* (fld_with_cube_root.cubrt 
        (quadratic_formula f myfld.one (d) 
                (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one))) (mul_nonzero f (three f) (fld_with_cube_root.cubrt 
        (quadratic_formula f myfld.one (d) 
                (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one)) fld_not_char_three.not_char_three
                                                                            (cubrt_nonzero f (quadratic_formula f myfld.one (d) (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one) (cardano_den_ne_zero f c d c_ne_zero)))))),
  split,
  unfold cardano_formula_new,

  apply depressed_cubic_simultaneous_solution,

  exact c_ne_zero,
  apply cubrt_eq, rw double_negative, refl,
end

def cubic_subst (f : Type) [myfld f] (a b c d x : f) : f := 
  (a .* (cubed f x)) .+ ((b .* (square f x)) .+ ((c .* x) .+ d))

lemma divide_cubic_through (f : Type) [myfld f] (a b c d x : f) (a_ne_zero : a ≠ myfld.zero) : 
      (cubic_subst f a b c d x) = myfld.zero <-> 
      (cubic_subst f myfld.one (b .* (myfld.reciprocal a a_ne_zero)) (c .* (myfld.reciprocal a a_ne_zero)) (d .* (myfld.reciprocal a a_ne_zero)) x)
       = myfld.zero := 
begin 
  unfold cubic_subst, split, intros h, 
  have h1 : (((a .* (cubed f x)) .+ ((b .* (square f x)) .+ ((c .* x) .+ d))) .* (myfld.reciprocal a a_ne_zero)) = myfld.zero, 
    rw h, rw mul_zero, 
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
    rw h, rw mul_zero, 
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
  := ((cardano_formula_a_new f (((square f (b .* (myfld.reciprocal a a_ne_zero))) .* (.- (third f))) .+ (c .* (myfld.reciprocal a a_ne_zero))) ((twenty_seventh f) .* ((((two f) .* (cubed f (b .* (myfld.reciprocal a a_ne_zero)))) .+ (.- ((nine f) .* ((b .* (myfld.reciprocal a a_ne_zero)) .* (c .* (myfld.reciprocal a a_ne_zero)))))) .+ ((twenty_seven f) .* (d .* (myfld.reciprocal a a_ne_zero))))) (int_quantity_ne_zero_simp f a b c a_ne_zero int_quantity_ne_zero)) .+ (.- ((b .* (myfld.reciprocal a a_ne_zero)) .* (third f))))

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
  clear tmp, unfold cubic_formula_a, unfold cardano_formula_a_new, 
  rw <- myfld.add_assoc (cardano_formula_new f _ _ _ _ _ _) (.- _) _, 
  rw myfld.add_comm (.- _) _, rw myfld.add_negate _, rw zero_simp f _, 
  exact cardano_works f _ _ _ _ _ _,
end 



/- I was hoping to be able to prove the formulae formations equivalent, but that's unfortunately impossible.
    We end up needing to prove that sqrt (x)/2 = sqrt(x/4).
    This is obviously true for any sensible sqrt function, but our minimalist specification of square roots means it isn't
    necessarily true of any valid implementation.-/

/- def cardano_formula_old (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d : f) (c_ne_zero : c ≠ myfld.zero) (cubrt_func : f -> f)
      (cubrt_func_nonzero : ∀ (x : f), x ≠ myfld.zero -> (cubrt_func x ≠ myfld.zero))
      (cubrt_func_correct : ∀ (x : f), (cubed f (cubrt_func x)) = x) : f := 
  ((cubrt_func ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) .+ (.- (c .* (myfld.reciprocal ((cubrt_func ((cardano_intermediate_val f c d) .+ (cardano_other_int_val f d))) .* (three f)) (cardano_denominator_not_zero f c d c_ne_zero cubrt_func cubrt_func_nonzero)))))

lemma cardano_versions_equiv (f : Type) [myfld f] [fld_with_sqrt f] [fld_with_cube_root f] [fld_not_char_two f] [fld_not_char_three f] 
      (c d : f) (c_ne_zero : c ≠ myfld.zero) (cubrt_func : f -> f)
      (cubrt_func_nonzero : ∀ (x : f), x ≠ myfld.zero -> (cubrt_func x ≠ myfld.zero))
      (cubrt_func_correct : ∀ (x : f), (cubed f (cubrt_func x)) = x) :
  (cardano_formula_new f c d c_ne_zero cubrt_func cubrt_func_nonzero cubrt_func_correct) =
  (cardano_formula_old f c d c_ne_zero cubrt_func cubrt_func_nonzero cubrt_func_correct) :=
begin
  have clear_term : ∀ (a b x : f), a = b -> (x .+ a) = (x .+ b), 
    intros a b x h, rw h, 
  unfold cardano_formula_new, unfold cardano_formula_old,
  have reduce_1 : ((quadratic_formula f myfld.one d (.- (cubed f c) .* (myfld.reciprocal (twenty_seven f) (twenty_seven_ne_zero f))) myfld.zero_distinct_one))
              =
        (cardano_intermediate_val f c d) .+ (cardano_other_int_val f d),
    unfold quadratic_formula, unfold cardano_intermediate_val, unfold cardano_other_int_val,
    rw one_mul_simp, rw reciprocal_rewrite f _ _ (simp_mul_one f _),
    rw distrib_simp,
    repeat {rw mul_negate}, repeat {rw mul_negate_alt_simp}, rw double_negative,
    rw myfld.add_comm _ (.- (d .* (myfld.reciprocal (two f) fld_not_char_two.not_char_two))),
    rw only_one_reciprocal f (two f) _ (fld_not_char_two.not_char_two),
    apply clear_term,
end
-/
