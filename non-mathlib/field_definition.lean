class myfld (f : Type) := 
(add : f -> f -> f)
(mul : f -> f -> f)
(negate : f -> f)
(zero : f)
(reciprocal : ∀ (x : f), (x ≠ zero) -> f) /- Reciprocal of zero is undefined.-/ 
(one : f)
(add_assoc : ∀ (x y z : f), (add x (add y z)) = (add (add x y) z))
(mul_assoc : ∀ (x y z : f), (mul x (mul y z)) = (mul (mul x y) z))
(add_comm : ∀ (x y : f), (add x y) = (add y x))
(mul_comm : ∀ (x y : f), (mul x y) = (mul y x))
(add_zero : ∀ (x : f), x = (add x zero))
(mul_one : ∀ (x : f), x = (mul x one))
(add_negate : ∀ (x : f), (add x (negate x)) = zero)
(mul_reciprocal : ∀ (x : f), ∀ (proof : x ≠ zero), (mul x (reciprocal x proof)) = one)
(distrib : ∀ (x y z : f), (add (mul x z) (mul y z)) = (mul (add x y) z))
(zero_distinct_one : one ≠ zero) /- By definition, 0 and 1 can't be the same element. -/ 

infix ` .+ `:1000000 := myfld.add
infix ` .* `:1000001 := myfld.mul
prefix ` .- `:1000002 := myfld.negate

def square (f : Type) [myfld f] : f -> f 
| x := x .* x 

@[simp] lemma add_comm (f : Type) [myfld f] (x y : f) : x .+ y = y .+ x := 
begin 
  exact (myfld.add_comm : ∀ (x y : f), (x .+ y) = (y .+ x)) x y, 
end 

@[simp] lemma one_mul_simp (f : Type) [myfld f] (x : f) : myfld.one .* x = x := 
begin 
  rw myfld.mul_comm, have h : x = x .* myfld.one, exact myfld.mul_one x, cc, 
end 


@[simp] lemma add_assoc (f : Type) [myfld f] (x y z : f) : ((x .+ y) .+ z) = (x .+ (y .+ z)) := 
begin 
  symmetry, exact myfld.add_assoc x y z, 
end 

@[simp] lemma mul_comm (f : Type) [myfld f] (x y : f) : x .* y = y .* x := 
begin 
  exact myfld.mul_comm x y, 
end 

@[simp] lemma mul_assoc (f : Type) [myfld f] (x y z : f) : ((x .* y) .* z) = (x .* (y .* z)) := 
begin 
  symmetry, exact myfld.mul_assoc x y z, 
end 

lemma zero_add (f : Type) [myfld f] (x : f) : x = (myfld.zero : f) .+ x := 
begin 
  rw add_comm f (myfld.zero : f) x, 
  exact (myfld.add_zero : ∀ (x : f), x = (x .+ myfld.zero)) x, 
end 

@[simp] lemma zero_simp (f : Type) [myfld f] (x : f) : (x .+ myfld.zero) = x := 
begin 
  symmetry, exact myfld.add_zero x, 
end 

@[simp] lemma simp_zero (f : Type) [myfld f] (x : f) : (myfld.zero .+ x) = x := 
begin 
  symmetry, exact zero_add f x, 
end 

@[simp] lemma distrib_simp (f : Type) [myfld f] (x y z : f) : ((x .+ y) .* z) = ((x .* z) .+ (y .* z)) := 
begin 
  symmetry, exact myfld.distrib x y z, 
end 

@[simp] lemma distrib_simp_alt (f : Type) [myfld f] (x y z : f) : (x .* (y .+ z)) = (x .* y) .+ (x .* z) := 
begin 
  rw myfld.mul_comm x (y .+ z), rw myfld.mul_comm x y, rw myfld.mul_comm x z, 
  exact distrib_simp f y z x, 
end 

@[simp] lemma one_mul (f : Type) [myfld f] (x : f) : (myfld.one : f) .* x = x := 
begin 
  rw (myfld.mul_comm), symmetry, exact (myfld.mul_one) x, 
end 

@[simp] lemma simp_mul_one (f : Type) [myfld f] (x : f) : x .* (myfld.one : f) = x := 
begin 
  rw myfld.mul_comm, exact one_mul f x, 
end 

@[simp] lemma add_negate_simp (f : Type) [myfld f] (x : f) : x .+ .-x = myfld.zero := 
begin 
  exact myfld.add_negate x, 
end 

@[simp] lemma add_negate_simp_alt (f : Type) [myfld f] (x : f) : (.- x) .+ x = myfld.zero := 
begin 
  rw myfld.add_comm (.- x) x, exact add_negate_simp f x, 
end 

@[simp] lemma mul_reciprocal (f : Type) [myfld f] (x : f) (proof : x ≠ myfld.zero) : 
                x .* (myfld.reciprocal x proof) = myfld.one := 
begin 
  exact myfld.mul_reciprocal x proof, 
end 

lemma equal_ne_zero (f : Type) [myfld f] (x y : f) : (x = y) -> (x ≠ myfld.zero) -> (y ≠ myfld.zero) := 
begin 
  intros h1 h2, rw h1 at h2, exact h2, 
end 