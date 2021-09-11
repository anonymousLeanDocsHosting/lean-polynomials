import field

inductive  item_plus_sqrt (f : Type) [myfld f] (rt : f) : Type
| ips : f -> f -> item_plus_sqrt

open item_plus_sqrt

def ips_zero (f : Type) [myfld f] (rt : f) : (item_plus_sqrt f rt) := ips myfld.zero myfld.zero

def ips_add (f : Type) [myfld f] (rt : f) : (item_plus_sqrt f rt) -> (item_plus_sqrt f rt) -> (item_plus_sqrt f rt)
| (ips a b) (ips c d) := (ips (myfld.add a c) (myfld.add b d))

def ips_negate (f : Type) [myfld f] (rt : f) : (item_plus_sqrt f rt) -> (item_plus_sqrt f rt)
| (ips a b) := (ips (myfld.negate a) (myfld.negate b))

def ips_mul (f : Type) [myfld f] (rt : f) : (item_plus_sqrt f rt) -> (item_plus_sqrt f rt) -> (item_plus_sqrt f rt)
| (ips a b) (ips c d) := (ips ((a .* c) .+ (b .* d .* rt)) ((a .* d) .+ (b .* c)))

def to_ips (f : Type) [myfld f] (rt : f) (x : f) : (item_plus_sqrt f rt) := (ips x myfld.zero)

lemma ips_add_comm (f : Type) [myfld f] (rt : f) (a b c d : f) :
  ips_add f rt (ips a b) (ips c d) = ips_add f rt (ips c d) (ips a b) :=
begin
  unfold ips_add, rw myfld.add_comm a c, rw myfld.add_comm b d,
end

lemma ips_add_assoc (f : Type) [myfld f] (rt : f) (a1 b1 a2 b2 a3 b3 : f) :
  ips_add f rt (ips a1 b1) (ips_add f rt (ips a2 b2) (ips a3 b3)) = 
  ips_add f rt (ips_add f rt (ips a1 b1) (ips a2 b2)) (ips a3 b3) :=
begin
  unfold ips_add, repeat {rw myfld.add_assoc},
end

lemma ips_mul_comm (f : Type) [myfld f] (rt : f) (a b c d : f) :
  ips_mul f rt (ips a b) (ips c d) = ips_mul f rt (ips c d) (ips a b) :=
begin
  unfold ips_mul, rw myfld.mul_comm a c, rw myfld.mul_comm b d,
  rw myfld.mul_comm a d, rw myfld.mul_comm b c,
  rw myfld.add_comm (c .* b) (d .* a),
end

def quadratic_formula (f : Type) [myfld f] [fld_not_char_two f] (b c : f) : 
      (item_plus_sqrt f ((b .* b) .+ ((four f) .* .- c))) :=
  ips (.- b) .* (myfld.reciprocal (two f) (fld_not_char_two.not_char_two))
      (myfld.reciprocal (two f) (fld_not_char_two.not_char_two))

def quadratic_subst_ips (f : Type) [myfld f] [fld_not_char_two f] (rt : f) (b c : f) 
    (x : item_plus_sqrt f rt) : (item_plus_sqrt f rt) :=
  ips_add f rt (ips_mul f rt x x) (ips_add f rt (ips_mul f rt x (to_ips f rt b)) (to_ips f rt c))

lemma quadratic_formula_works (f : Type) [myfld f] [fld_not_char_two f] (b c : f) :
  (quadratic_subst_ips f ((b .* b) .+ ((four f) .* .- c)) b c
                        (quadratic_formula f b c))
                        =
  (ips myfld.zero myfld.zero) :=
begin
  unfold quadratic_formula, unfold quadratic_subst_ips,
  unfold to_ips, unfold ips_mul, unfold ips_add,
  repeat {rw zero_simp}, repeat {rw zero_mul}, repeat {rw mul_zero}, rw simp_zero, rw zero_simp,
  repeat {rw mul_negate, rw mul_negate_alt_simp}, rw mul_negate,
  rw double_negative,
  have tmp : ∀ (p q rt : f), (p = myfld.zero) -> (q = myfld.zero) ->
                ((ips p q) : (item_plus_sqrt f rt)) = 
                ((ips myfld.zero myfld.zero) : (item_plus_sqrt f rt)),
    intros p q rt h1 h2, rw h1, rw h2,
  apply tmp, clear tmp,
  rw mul_two_reciprocals,
  rw [myfld.mul_comm b (myfld.reciprocal (two f) _)] {occs := occurrences.pos [2]},
  rw <- myfld.mul_assoc _ (myfld.reciprocal (two f) _) _,
  rw myfld.mul_assoc (myfld.reciprocal (two f) _) (myfld.reciprocal (two f) _) _,
  rw mul_two_reciprocals, rw myfld.mul_comm b ((myfld.reciprocal _ _) .* _),
  rw <- myfld.mul_assoc (myfld.reciprocal _ _) b b,
  rw <- distrib_simp_alt,
  have tmp : .- (b .* (myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* b) =
              .- ((myfld.reciprocal ((two f) .* (two f)) (mul_nonzero f (two f) (two f) fld_not_char_two.not_char_two fld_not_char_two.not_char_two))
              .* ((b .* b) .+ (b .* b))),
    rw <- mul_two_reciprocals, have tmp_tmp : ((b .* b) .+ (b .* b)) = (two f) .* (b .* b),
      unfold two, rw distrib_simp, rw one_mul_simp,
    rw tmp_tmp, rw myfld.mul_assoc _ (two f) _, 
    rw <- myfld.mul_assoc _ (myfld.reciprocal (two f) _) (two f),
    rw myfld.mul_comm (myfld.reciprocal (two f) _) (two f), rw myfld.mul_reciprocal,
    rw simp_mul_one, rw myfld.mul_comm b _, rw myfld.mul_assoc,
  rw tmp, clear tmp, rw mul_negate_alt f _ ((b .* b) .+ (b .* b)),
  rw myfld.add_assoc, rw <- distrib_simp_alt,
  rw myfld.add_assoc (b .* b) (b .* b), rw myfld.add_comm _ (.- ((four f) .* c)),
  rw <- myfld.add_assoc _ ((b .* b) .+ (b .* b)) _,
  rw myfld.add_negate, rw zero_simp,
  rw mul_negate_alt_simp, have tmp : (two f) .* (two f) = (four f), unfold four, rw two_plus_two,
  rw reciprocal_rewrite f _ (four f) tmp, rw myfld.mul_assoc, rw myfld.mul_comm _ (four f),
  rw myfld.mul_reciprocal, rw one_mul_simp, rw myfld.add_comm, rw myfld.add_negate,

  clear tmp,
  rw myfld.mul_comm _ (b .* (myfld.reciprocal (two f) fld_not_char_two.not_char_two)),
  rw <- add_negate, rw <- distrib_simp_alt, rw only_one_reciprocal f (two f) _ (two_ne_zero f),
  rw add_two_halves, rw simp_mul_one,
  rw myfld.add_comm, rw myfld.mul_comm b _, rw myfld.add_negate,
end
