import field_definition

lemma mul_cancel (f : Type) [myfld f] (a b x : f) (x_ne_zero : x ≠ myfld.zero) : (a .* x) = (b .* x) -> a = b := 
begin 
  intros h, 
  have h1 : (a .* x) .* (myfld.reciprocal x x_ne_zero) = (b .* x) .* (myfld.reciprocal x x_ne_zero) , 
    rw h, 
  rw <- myfld.mul_assoc at h1, rw <- myfld.mul_assoc at h1, rw myfld.mul_reciprocal x x_ne_zero at h1, 
  rw <- myfld.mul_one a at h1, rw <- myfld.mul_one b at h1, exact h1, 
end 

lemma add_cancel (f : Type) [myfld f] (a b x : f) : (a = b) -> (x .+ a) = (x .+ b) := 
begin 
  intros h, rw h, 
end 

lemma add_cancel_inv (f : Type) [myfld f] (a b x : f) : (a .+ x) = (b .+ x) -> (a = b) := 
begin 
  intros h, 
  have h1 : (a .+ x) .+ (.- x) = (b .+ x) .+ (.- x) , 
    rw h, clear h, rename h1 h, 
  repeat {rw <- myfld.add_assoc at h}, repeat {rw myfld.add_negate x at h}, repeat {rw zero_simp at h}, 
  exact h, 
end 

/- Start by proving various elementary notions about general fields.-/ 

lemma only_one_reciprocal (f : Type) [myfld f] (x : f) (a b : x ≠ myfld.zero) : 
      (myfld.reciprocal x a) = (myfld.reciprocal x b) := 
begin 
  have h1 : x .* (myfld.reciprocal x a) = myfld.one, 
    exact myfld.mul_reciprocal x a, 
  have h2 : (myfld.reciprocal x b) .* myfld.one = myfld.reciprocal x b, 
    exact simp_mul_one f (myfld.reciprocal x b), 
  rw <- h1 at h2, 
end 

@[simp] lemma mul_zero (f : Type) [myfld f] (x : f) : (myfld.zero : f) .* x = (myfld.zero : f) := 
begin 
  have h1 : (myfld.zero : f) .* x = 
      ((myfld.zero : f) .* x) .+ (myfld.zero : f) , 
    exact myfld.add_zero ((myfld.zero : f) .* x), 
  have h2 : myfld.zero = (myfld.zero .* x) .+ (.- (myfld.zero .* x)) , 
    symmetry, exact myfld.add_negate (myfld.zero .* x), 
  rewrite [h2] at h1 {occs := occurrences.pos [3]}, 
  rw myfld.add_assoc at h1, rw myfld.distrib at h1, rw <- myfld.add_zero myfld.zero at h1, 
  rw myfld.add_negate at h1, exact h1, 
end 

@[simp] lemma zero_mul (f : Type) [myfld f] (x : f) : x .* myfld.zero = myfld.zero := 
begin 
  rw myfld.mul_comm, exact mul_zero f x, 
end 

lemma only_one_reciprocal_alt (f : Type) [myfld f] (a b : f) (a_ne_zero : a ≠ myfld.zero) : 
      (a .* b = myfld.one) -> b = (myfld.reciprocal a a_ne_zero) := 
begin 
  intro h,
  have h1 : (a .* b) .* (myfld.reciprocal a a_ne_zero) = myfld.one .* (myfld.reciprocal a a_ne_zero) , 
    rw h, 
  clear h, rename h1 h, 
  rw myfld.mul_comm (a .* b) _ at h, rw myfld.mul_assoc at h, 
  rw myfld.mul_comm (myfld.reciprocal _ _) a at h, rw myfld.mul_reciprocal a a_ne_zero at h, 
  repeat {rw one_mul f _ at h}, exact h, 
end 

@[simp] lemma negate_zero_zero (f : Type) [myfld f] : .- myfld.zero = (myfld.zero : f) := 
begin 
  symmetry, 
  have h1 : ((myfld.zero : f) .+ (.- (myfld.zero : f))) = (myfld.zero : f), 
    exact (myfld.add_negate : ∀ (x : f), (x .+ (.- x)) = myfld.zero) (myfld.zero : f), 
  have h2 : ((myfld.zero : f) .+ (.- (myfld.zero : f))) = 
            .- (myfld.zero : f), 
    symmetry, exact zero_add f (.- (myfld.zero : f)), 
  rw h1 at h2, exact h2, 
end 

lemma negate_ne_zero (f : Type) [myfld f] (a : f) : (a ≠ myfld.zero) -> ((.- a) ≠ myfld.zero) := 
begin 
  intros h1 h2, 
  have h3 : myfld.zero .+ a = (.- a) .+ a,
    rw h2, 
  rw simp_zero at h3, rw myfld.add_comm at h3, rw myfld.add_negate a at h3, cc, 
end 

@[simp] lemma recip_one_one (f : Type) [myfld f] (one_ne_zero : (myfld.one : f) ≠ (myfld.zero : f)) : 
        (myfld.reciprocal myfld.one one_ne_zero) = (myfld.one : f) := 
begin 
  have h1 : myfld.one .* (myfld.reciprocal myfld.one one_ne_zero) = myfld.one, 
    exact myfld.mul_reciprocal myfld.one (one_ne_zero : ((myfld.one : f) ≠ (myfld.zero : f))), 
  have h2 : myfld.one .* (myfld.reciprocal myfld.one one_ne_zero) = (myfld.reciprocal myfld.one one_ne_zero), 
    exact one_mul f (myfld.reciprocal myfld.one one_ne_zero), 
  rw h1 at h2, symmetry, exact h2, 
end 

@[simp] lemma double_negative (f : Type) [myfld f] (x : f) : .- .- x = x := 
begin 
  have h1 : x .+ (myfld.zero : f) = x, 
    symmetry, exact (myfld.add_zero : ∀ (x : f), x = x .+ (myfld.zero : f)) x, 
  have h2 : (.- x) .+ (.- .- x) = 
                (myfld.zero : f), 
    exact (myfld.add_negate : ∀ (x : f), (x .+ (.- x)) = (myfld.zero : f))
          (.- x), 
  rw <- h2 at h1, 
  rw myfld.add_assoc at h1, rw myfld.add_negate at h1, rw <- zero_add f (.- (.- x)) at h1, 
  exact h1, 
end 

lemma reciprocal_ne_zero (f : Type) [myfld f] (x : f) (x_ne_zero : x ≠ myfld.zero) : 
    myfld.reciprocal x x_ne_zero ≠ myfld.zero := 
begin 
  have x_mul_zero : x .* myfld.zero = myfld.zero, 
      exact zero_mul f x, 
  intro recip_eq_zero, 
  have x_mul_recip_eq_zero : myfld.zero = x .* (myfld.reciprocal x x_ne_zero) , 
    rw <- recip_eq_zero at x_mul_zero, rw [recip_eq_zero] at x_mul_zero {occs := occurrences.pos [2]}, 
    symmetry, exact x_mul_zero, 
  rw [x_mul_recip_eq_zero] at x_mul_zero {occs := occurrences.pos [1]}, 
  rw myfld.mul_reciprocal x x_ne_zero at x_mul_zero, rw <- myfld.mul_one x at x_mul_zero, 
  exact x_ne_zero x_mul_zero, 
end 

@[simp] lemma double_reciprocal (f : Type) [myfld f] (x : f) (x_ne_zero : x ≠ myfld.zero)
: (myfld.reciprocal (myfld.reciprocal x x_ne_zero) (reciprocal_ne_zero f x x_ne_zero)) = x := 
begin 
  have h1 : x .* (myfld.one : f) = x, 
    symmetry, exact myfld.mul_one x, 
  rw <- myfld.mul_reciprocal (myfld.reciprocal x x_ne_zero) (reciprocal_ne_zero f x x_ne_zero) at h1, 
  rw myfld.mul_assoc x (myfld.reciprocal x x_ne_zero) at h1, 
  rw myfld.mul_reciprocal x at h1, rw one_mul f (myfld.reciprocal (myfld.reciprocal x x_ne_zero) (reciprocal_ne_zero f x x_ne_zero)) at h1, exact h1, 
end 

lemma double_reciprocal_inv (f : Type) [myfld f] (x : f) (x_ne_zero : x ≠ myfld.zero) : 
                            x = myfld.reciprocal (myfld.reciprocal x x_ne_zero) (reciprocal_ne_zero f x x_ne_zero) := 
begin 
  symmetry, exact double_reciprocal f x x_ne_zero, 
end 

@[simp] lemma mul_negate (f : Type) [myfld f] (x y : f) : .- x .* y = 
                                                  .- (x .* y) := 
begin 
  have h1 : y .* (myfld.zero : f) = (myfld.zero : f), 
    rw myfld.mul_comm, exact mul_zero f y, 
  have h2 : (myfld.zero : f) = x .+ .- x , 
    symmetry, exact myfld.add_negate x, 
  rw [h2] at h1 {occs := occurrences.pos [1]}, 
  rw myfld.mul_comm at h1, rw <- myfld.distrib at h1, 
  have h3 : (.- (y .* x)) .+ myfld.zero = (.- (y .* x)), 
    symmetry, exact myfld.add_zero (.- (y .* x)), 
  rw <- h1 at h3, rw myfld.add_assoc at h3, rw myfld.add_comm (.- (y .* x)) (x .* y) at h3, 
  rw myfld.mul_comm y x at h3, rw myfld.add_negate at h3, rw <- zero_add f ((.- x) .* y) at h3, 
  exact h3, 
end 

@[simp] lemma mul_negate_alt_simp (f : Type) [myfld f] (x y : f) : (x .* (.- y)) = .- (x .* y) := 
begin 
  rw myfld.mul_comm, rw myfld.mul_comm x y, exact mul_negate f y x, 
end 

lemma mul_negate_alt (f : Type) [myfld f] (x y : f) : .- (x .* y) = (x .* (.- y)) := 
begin 
  symmetry, rw myfld.mul_comm, rw myfld.mul_comm x y, exact mul_negate f y x, 
end 

@[simp] lemma add_negate (f : Type) [myfld f] (x y : f) : (.- (x .+ y)) = 
                                                  ((.- x) .+ (.- y)) := 
begin 
  have h1 : ((x .+ y) .+ (.- (x .+ y))) = myfld.zero, 
    exact myfld.add_negate (x .+ y), 
  have h2 : (((.- x) .+ (.- y)) .+ myfld.zero) = ((.- x) .+ (.- y)), 
    symmetry, exact myfld.add_zero ((.- x) .+ (.- y)), 
  rw <- h1 at h2, 
  rw myfld.add_comm x y at h2, repeat {rw myfld.add_assoc _ _ _ at h2}, 
  rw myfld.add_comm (((.- x) .+ (.- y)) .+ y) x at h2, 
  simp at h2, exact h2, 
end 

lemma mul_nonzero (f : Type) [myfld f] (x y : f) (x_ne_zero : x ≠ myfld.zero) (y_ne_zero : y ≠ myfld.zero) : 
                                            (x .* y) ≠ myfld.zero := 
begin 
  intro h, 
  have h1 : x .* (myfld.reciprocal x x_ne_zero) = myfld.one, 
    exact myfld.mul_reciprocal x x_ne_zero, 
  have h2 : y = y .* myfld.one,
    exact myfld.mul_one y, 
  rw <- h1 at h2, rw myfld.mul_assoc _ _ _ at h2, 
  rw myfld.mul_comm y x at h2, rw h at h2, 
  rw mul_zero f _ at h2, exact y_ne_zero h2, 
end 

@[simp] lemma mul_two_reciprocals (f : Type) [myfld f] (x y : f) (x_ne_zero : x ≠ myfld.zero) (y_ne_zero : y ≠ myfld.zero) : 
                                              ((myfld.reciprocal x x_ne_zero) .* (myfld.reciprocal y y_ne_zero)) = 
                                              (myfld.reciprocal (x .* y) (mul_nonzero f x y x_ne_zero y_ne_zero)) := 
begin 
  have h1 : (x .* y) .* (myfld.reciprocal (x .* y) (mul_nonzero f x y x_ne_zero y_ne_zero)) = myfld.one, 
    exact myfld.mul_reciprocal (x .* y) (mul_nonzero f x y x_ne_zero y_ne_zero), 
  have h2 : ((myfld.reciprocal x x_ne_zero) .* (myfld.reciprocal y y_ne_zero)) .* myfld.one = 
                       (myfld.reciprocal x x_ne_zero) .* (myfld.reciprocal y y_ne_zero) , 
    symmetry, exact myfld.mul_one ((myfld.reciprocal x x_ne_zero) .* (myfld.reciprocal y y_ne_zero)), 
  rw <- h1 at h2, 
  repeat {rw myfld.mul_assoc _ _ _ at h2}, 
  rw myfld.mul_comm ((((myfld.reciprocal x x_ne_zero) .* (myfld.reciprocal y y_ne_zero)) .* x) .* y)
                     (myfld.reciprocal (x .* y) (mul_nonzero f x y x_ne_zero y_ne_zero)) at h2, 
  symmetry, simp at h2, exact h2, 
end 

lemma factor_1_ne_zero (f : Type) [myfld f] (x y : f) : (x .* y) ≠ myfld.zero -> x ≠ myfld.zero := 
begin 
  intro prod_n_zero, intro x_zero, rw x_zero at prod_n_zero, rw mul_zero f y at prod_n_zero, 
  have tmp : myfld.zero = myfld.zero, 
    refl, exact prod_n_zero tmp, 
end 

lemma factor_2_ne_zero (f : Type) [myfld f] (x y : f) : (x .* y) ≠ myfld.zero -> y ≠ myfld.zero := 
begin 
  rw myfld.mul_comm x y, exact factor_1_ne_zero f y x, 
end 

lemma split_reciprocal (f : Type) [myfld f] (x y : f) (xy_ne_zero : (x .* y ≠ myfld.zero)) : 
                        (myfld.reciprocal (x .* y) xy_ne_zero) = 
                        (myfld.reciprocal x (factor_1_ne_zero f x y xy_ne_zero)) .* (myfld.reciprocal y (factor_2_ne_zero f x y xy_ne_zero)) := 
begin 
  rw only_one_reciprocal f (x .* y) xy_ne_zero 
      (mul_nonzero f x y (factor_1_ne_zero f x y xy_ne_zero) (factor_2_ne_zero f x y xy_ne_zero)), 
  symmetry, 
  exact mul_two_reciprocals f x y (factor_1_ne_zero f x y xy_ne_zero) (factor_2_ne_zero f x y xy_ne_zero), 
end 

lemma cancel_from_reciprocal (f : Type) [myfld f] (x y : f) (xy_ne_zero : (x .* y ≠ myfld.zero)) : 
              ((myfld.reciprocal (x .* y) xy_ne_zero) .* x) = 
              (myfld.reciprocal y (factor_2_ne_zero f x y xy_ne_zero)) := 
begin 
  rw split_reciprocal f x y xy_ne_zero, 
  rw myfld.mul_comm (myfld.reciprocal x _) (myfld.reciprocal y _), rw <- myfld.mul_assoc, 
  rw myfld.mul_comm (myfld.reciprocal x _) x, rw myfld.mul_reciprocal x _, 
  rw simp_mul_one f _, 
end 

lemma cancel_from_reciprocal_alt (f : Type) [myfld f] (x y : f) (xy_ne_zero : (x .* y ≠ myfld.zero)) : 
              (x .* (myfld.reciprocal (x .* y) xy_ne_zero)) = 
              (myfld.reciprocal y (factor_2_ne_zero f x y xy_ne_zero)) := 
begin 
  rw myfld.mul_comm x (myfld.reciprocal _ _), exact cancel_from_reciprocal f x y xy_ne_zero, 
end 

lemma add_two_reciprocals (f : Type) [myfld f] (x y : f) (x_ne_zero : x ≠ myfld.zero) (y_ne_zero : y ≠ myfld.zero) : 
        ((myfld.reciprocal x x_ne_zero) .+ (myfld.reciprocal y y_ne_zero)) = 
        (x .+ y) .* (myfld.reciprocal (x .* y) (mul_nonzero f x y x_ne_zero y_ne_zero)) := 
begin 
  have h1 : (myfld.reciprocal x x_ne_zero) = y .* (myfld.reciprocal (x .* y) (mul_nonzero f x y x_ne_zero y_ne_zero)) , 
    rw split_reciprocal f x y _, rw myfld.mul_comm (myfld.reciprocal x _) (myfld.reciprocal y _), 
    rw myfld.mul_assoc y _ _, rw myfld.mul_reciprocal y _, rw one_mul_simp f _, 
  have h2 : (myfld.reciprocal y y_ne_zero) = x .* (myfld.reciprocal (x .* y) (mul_nonzero f x y x_ne_zero y_ne_zero)) , 
    rw split_reciprocal f x y _, 
    rw myfld.mul_assoc x _ _, rw myfld.mul_reciprocal x _, rw one_mul_simp f _, 
  rw h1, rw h2, clear h1, clear h2, 
  rw <- distrib_simp f y x _, rw myfld.add_comm y x, 
end 

lemma only_one_negation (f : Type) [myfld f] (a b : f) : a .+ b = myfld.zero -> b = .- a := 
begin 
  intros h, have h1 : (a .+ b) .+ (.- b) = .- b, 
    rw h, rw simp_zero, 
  rw <- myfld.add_assoc _ _ _ at h1, rw myfld.add_negate at h1, rw zero_simp at h1, 
  have h2 : .- (.- b) = .- a, 
    have triv : .- a = .- a, refl, 
    rw h1 at triv {occs := occurrences.pos [1]}, exact triv, 
  rw double_negative f _ at h2, exact h2, 
end 

/- We need this later. 
   By default Lean doesn't let us use rewrites on reciprocals. 
   This is because myfld.reciprocal takes both an element of the field and a proof that it is not zero. 
   Ergo, if we have (reciprocal x x_ne_zero) and try to rewrite it with the hypothesis x = y... 
      we end up with (reciprocal y x_ne_zero) which is nonsense and isn't allowed. 
   This lemma will let us get around that by utilizing the fact that x = y means that x ≠ 0 -> y ≠ 0.-/ 
lemma reciprocal_rewrite (f : Type) [myfld f] (x y : f) (equal_proof : x = y) (x_ne_zero : x ≠ myfld.zero) : 
      (myfld.reciprocal x x_ne_zero) = (myfld.reciprocal y (equal_ne_zero f x y equal_proof x_ne_zero)) := 
begin 
  have h1 : x .* (myfld.reciprocal x x_ne_zero) = myfld.one, 
    exact myfld.mul_reciprocal x x_ne_zero, 
  rw equal_proof at h1 {occs := occurrences.pos[1]}, 
  have h2 : (myfld.reciprocal y (equal_ne_zero f x y equal_proof x_ne_zero)) = 
            (myfld.reciprocal y (equal_ne_zero f x y equal_proof x_ne_zero)) .* myfld.one,
    exact myfld.mul_one (myfld.reciprocal y (equal_ne_zero f x y equal_proof x_ne_zero)), 
  rw <- h1 at h2, 
  rw myfld.mul_assoc at h2, rw myfld.mul_comm _ y at h2, rw myfld.mul_reciprocal y _ at h2, 
  rw one_mul f _ at h2, symmetry, exact h2, 
end 

/- We need this later and doing it here will end up saving time.-/ 
lemma assoc_tree (f : Type) [myfld f] (a b c d : f) : 
    ((a .+ b) .+ (c .+ d)) = (a .+ ((b .+ c) .+ d)) := 
begin 
  rw <- myfld.add_assoc a b (c .+ d), rw myfld.add_assoc b c d, 
end 
lemma assoc_tree_mul (f : Type) [myfld f] (a b c d : f) : 
    ((a .* b) .* (c .* d)) = (a .* ((b .* c) .* d)) := 
begin 
  rw <- myfld.mul_assoc a b (c .* d), rw myfld.mul_assoc b c d, 
end 

lemma multiply_two_squares (f : Type) [myfld f] (a b : f) : 
    (square f a) .* (square f b) = square f (a .* b) := 
begin 
  unfold square, rw myfld.mul_assoc (a .* a) b b, 
  rw <- myfld.mul_assoc a a b, 
  have tmp : (a .* (a .* b)) .* b = (a .* (b .* a)) .* b,
    rw myfld.mul_comm a b, 
  rw tmp, clear tmp, 
  rw myfld.mul_assoc a b a, rw <- myfld.mul_assoc (a .* b) a b, 
end 

lemma mul_zero_by_reciprocal (f : Type) [myfld f] (a b : f) (a_ne_zero : a ≠ myfld.zero) : 
  b = myfld.zero <-> b .* (myfld.reciprocal a a_ne_zero) = myfld.zero := 
begin 
  split, 
    intros h, rw h, exact mul_zero f _, 
    intros h, have h1 : (b .* (myfld.reciprocal a a_ne_zero)) .* a = myfld.zero, 
      rw h, rw mul_zero, 
    rw <- myfld.mul_assoc at h1, rw myfld.mul_comm _ a at h1, rw myfld.mul_reciprocal a a_ne_zero at h1, 
    rw simp_mul_one at h1, exact h1, 
end 

lemma negate_zero (f : Type) [myfld f] (a : f) : a = myfld.zero <-> (.- a) = myfld.zero := 
begin 
  split, intros h, 
  have h1 : (.- a) .+ myfld.zero = myfld.zero, 
    rw h, rw myfld.add_comm, exact myfld.add_negate (myfld.zero), 
  rw <- myfld.add_zero (.- a) at h1, exact h1,

  intros h, have h1 : .- .- a = myfld.zero, rw h, exact negate_zero_zero f,
  rw double_negative at h1, exact h1, 
end 

lemma negate_zero_a (f : Type) [myfld f] (a : f) : a = myfld.zero -> (.- a) = myfld.zero :=
begin
  rw negate_zero, cc,
end 

lemma carry_term_across (f : Type) [myfld f] (a b x : f) : a .+ x = b <-> a = b .+ (.- x) := 
begin 
  split, 
  intros h, 
  have h1 : (a .+ x) .+ (.- x) = b .+ (.- x) , 
    rw h, 
  rw <- myfld.add_assoc _ _ _ at h1, rw myfld.add_negate _ at h1, rw zero_simp f _ at h1, exact h1, 

  intros h, 
  have h1 : a .+ x = (b .+ (.- x)) .+ x,
    rw h, 
  rw <- myfld.add_assoc _ _ _ at h1, rw myfld.add_comm (.- x) x at h1, 
  rw myfld.add_negate x at h1, rw zero_simp f _ at h1, exact h1, 
end 

lemma carry_term_across_alt (f : Type) [myfld f] (a b : f) : a = b <-> myfld.zero = b .+ (.- a) := 
begin 
  split, 
    intros h, rw <- h, rw myfld.add_negate, 
    intros h, rw myfld.add_zero a, rw h, rw myfld.add_comm b, rw myfld.add_assoc, rw myfld.add_negate, rw simp_zero, 
end 

lemma mul_both_sides (f : Type) [myfld f] (a b x : f) (x_ne_zero : x ≠ myfld.zero) : 
  a = b <-> (a .* x) = (b .* x) := 
begin 
  split, 
    intros h, rw h, 
    intros h, have h1 : (a .* x) .* (myfld.reciprocal x x_ne_zero) = (b .* x) .* (myfld.reciprocal x x_ne_zero) , 
      rw h, 
    repeat {rw <- myfld.mul_assoc at h1}, repeat {rw myfld.mul_reciprocal at h1}, repeat {rw simp_mul_one at h1}, 
    exact h1, 
end 

lemma mul_both_sides_ne (f : Type) [myfld f] (a b x : f) : a ≠ b -> x ≠ myfld.zero -> a .* x ≠ b .* x := 
begin 
    intros h1 x_ne_zero h2, 
    have cancel : a = b, 
      exact mul_cancel f a b x x_ne_zero h2, 
    cc, 
end 

lemma carry_term_across_ne (f : Type) [myfld f] (a b x : f) : a .+ x ≠ b <-> a ≠ b .+ (.- x) := 
begin 
  split, 
  intros h1 h2, rw <- carry_term_across f _ _ _ at h2, cc, 
  intros h1 h2, rw carry_term_across f _ _ _ at h2, cc, 
end 

def cubed (f : Type) [myfld f] : f -> f 
  | a := (a .* (a .* a))

def cube_of_product (f : Type) [myfld f] (a b : f) : (cubed f (a .* b)) = (cubed f a) .* (cubed f b) := 
begin 
  unfold cubed, simp only [mul_assoc f a _ _, myfld.mul_comm b a, myfld.mul_assoc b _ _], 
end 

def cube_nonzero (f : Type) [myfld f] (a : f) : a ≠ myfld.zero -> (cubed f a) ≠ myfld.zero := 
begin 
  intros a_ne_zero, unfold cubed, have a_sq_ne_zero : a .* a ≠ myfld.zero, 
      exact mul_nonzero f a a a_ne_zero a_ne_zero, 
  exact mul_nonzero f a (a .* a) a_ne_zero a_sq_ne_zero, 
end 

def cube_of_negative (f : Type) [myfld f] (a : f) : (cubed f (.- a)) = .- (cubed f a) := 
begin 
  unfold cubed, rw mul_negate_alt_simp f _ _, rw mul_negate f _ _, rw mul_negate f _ _, rw double_negative f _, 
end 

def cube_of_reciprocal (f : Type) [myfld f] (a : f) (a_ne_zero : a ≠ myfld.zero) : 
              (cubed f (myfld.reciprocal a a_ne_zero)) = myfld.reciprocal (cubed f a) (cube_nonzero f a a_ne_zero) := 
begin 
  unfold cubed, simp only [mul_two_reciprocals, only_one_reciprocal], 
end 

def factorized_cubic_expression (f : Type) [myfld f] (x a b c : f) : f := 
    (((x .+ (.- a)) .* (x .+ (.- b))) .* (x .+ (.- c)))

lemma ne_diff_not_zero (f : Type) [myfld f] (x y : f) : x ≠ y -> x .+ (.- y) ≠ myfld.zero := 
begin 
  intros ne h, 
  have tmp : (x .+ (.- y)) .+ y = myfld.zero .+ y,
    rw h, clear h, rename tmp h, 
  rw <- zero_add f y at h, rw <- myfld.add_assoc at h, rw myfld.add_comm _ y at h, rw myfld.add_negate y at h, 
  rw <- myfld.add_zero x at h, cc, 
end 

lemma multiply_out_cubic (f : Type) [myfld f] (x a b c : f) : (factorized_cubic_expression f x a b c) = 
   ((cubed f x) .+ ((.- ((a .+ (b .+ c)) .* (x .* x))) .+ ((x .* (((a .* b) .+ (a .* c)) .+ (b .* c))) .+ (.- (a .* (b .* c)))))) := 
begin 
  unfold cubed, unfold factorized_cubic_expression, 
  simp only [mul_negate, mul_negate_alt_simp, distrib_simp, distrib_simp_alt], 
  repeat {rw <- myfld.mul_assoc}, 
  simp only [myfld.mul_comm x _, myfld.mul_assoc _ x _, myfld.mul_assoc _ x x], 
  repeat {rw myfld.mul_assoc}, repeat {rw double_negative}, 
  repeat {rw <- myfld.add_assoc}, repeat {rw myfld.add_comm ((a .* b) .* x) }, 
  repeat {rw myfld.add_assoc}, repeat {rw add_negate}, repeat {rw <- myfld.add_assoc}, 
end 

/- Ergo we have demonstrated that if a field has a notion of cube roots (and a notion of square roots) then 
    every nonzero entry must have exactly three different cube roots.-/ 

/- (a + b) (a - b) = a^2 - b^2 
   Well-known, easy to prove, and useful.-/ 
lemma difference_of_squares (f : Type) [myfld f] (a b : f) : 
  (a .+ b) .* (a .+ (.- b)) = (square f a) .+ (.- (square f b)) := 
begin 
  unfold square, rw distrib_simp f _ _ _, repeat {rw distrib_simp_alt f _ _ _}, 
  repeat {rw <- mul_negate_alt f _ _}, rw myfld.mul_comm b a, 
  rw myfld.add_assoc _ (a .* b) _, rw <- myfld.add_assoc _ _ (a .* b), 
  rw myfld.add_comm (.- (a .* b)) (a .* b), 
  rw myfld.add_negate _, rw <- myfld.add_zero (a .* a), 
end 

/- This situation arises in one of my proof later and for some reason I can't get simp 
to do it automatically. It be like that sometimes. -/ 

lemma mul_complex (f : Type) [myfld f] (a b c d : f) : 
    (a .* (b .* c)) .* (a .* (d .* c)) = 
    ((a .* c) .* (a .* c)) .* (b .* d) := 
begin 
  repeat {rw <- myfld.mul_assoc _ _ _}, rw myfld.mul_comm c (b .* d), 
  rw <- myfld.mul_assoc b d c, repeat {rw myfld.mul_assoc _ _ _}, 
  rw myfld.mul_comm (_ .* _) b, repeat {rw myfld.mul_assoc _ _ _}, rw myfld.mul_comm b a, 
end 

lemma subtract_ne (f : Type) [myfld f] (a b : f) : 
    a ≠ b -> a .+ (.- b) ≠ myfld.zero := 
begin 
  intros h1 h2, 
  have h3 : (a .+ (.- b)) .+ b = (myfld.zero .+ b), 
    rw h2, 
  rw simp_zero at h3, rw <- myfld.add_assoc at h3, rw myfld.add_comm (.- b) b at h3, 
  rw myfld.add_negate b at h3, rw zero_simp at h3, cc, 
end 

lemma move_negation_ne (f : Type) [myfld f] (a b : f) : 
  a ≠ (.- b) <-> (.- a) ≠ b := 
begin 
  split, 
    intros h1 h2, rw <- h2 at h1, rw double_negative at h1, cc, 
    intros h1 h2, rw h2 at h1, rw double_negative at h1, cc, 
end 

lemma move_across (f : Type) [myfld f] (a b : f) : 
  a .+ b = myfld.zero <-> (.- a) = b := 
begin 
  split, 
    intros h, have h1 : (a .+ b) .+ (.- a) = myfld.zero .+ (.- a) , 
      rw h, 
    rw simp_zero at h1, rw <- myfld.add_assoc at h1, rw myfld.add_comm b _ at h1, 
    rw myfld.add_assoc at h1, rw myfld.add_negate at h1, rw simp_zero at h1, cc, 

    intros h, rw <- h, exact myfld.add_negate a, 
end 

@[simp] lemma square_negate (f : Type) [myfld f] (a : f) : (square f (.- a)) = (square f a) := 
begin 
  unfold square, rw mul_negate, rw mul_negate_alt_simp, rw double_negative, 
end 

@[simp] lemma cube_negate (f : Type) [myfld f] (a : f) : (cubed f (.- a)) = .- (cubed f a) := 
begin 
  unfold cubed, repeat {rw mul_negate}, repeat {rw mul_negate_alt_simp}, rw double_negative, 
end 

lemma mul_two_squares (f : Type) [myfld f] (a b : f) : (square f a) .* (square f b) = 
                                                       square f (a .* b) := 
begin 
  unfold square,repeat {rw myfld.mul_assoc}, rw myfld.mul_comm (a .* b) a, repeat {rw myfld.mul_assoc}, 
end 

lemma square_ne_zero (f : Type) [myfld f] (a : f) (a_ne_zero : a ≠ myfld.zero) : (square f a) ≠ myfld.zero := 
begin 
  unfold square, exact mul_nonzero f a a a_ne_zero a_ne_zero, 
end 

lemma reciprocal_squared (f : Type) [myfld f] (a : f) (a_ne_zero : a ≠ myfld.zero) : 
    (square f (myfld.reciprocal a a_ne_zero)) = (myfld.reciprocal (square f a) (square_ne_zero f a a_ne_zero)) := 
begin 
  unfold square, rw mul_two_reciprocals f a a a_ne_zero a_ne_zero, 
end 
