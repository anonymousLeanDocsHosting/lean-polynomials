import field_definition
import field_results
import numbers
import roots

def quadratic_subst (f : Type) [myfld f] : f -> f -> f -> f -> f 
| x a b c := (a .* (x .* x)) .+ ((b .* x) .+ c)

lemma complete_the_square (f : Type) [myfld f] (x b : f) : 
    (x .* x) .+ (((two f) .* b) .* x) = 
    (square f (x .+ b)) .+ (.- (square f b)) := 
begin 
  unfold square, unfold two, rw distrib_simp, rw distrib_simp_alt, repeat {rw distrib_simp}, rw one_mul, 
  repeat {rw <- myfld.add_assoc _ _ _}, rw myfld.add_negate _, rw zero_simp f _, rw myfld.mul_comm x b, 
end 

lemma multiply_out_squared (f : Type) [myfld f] (x a : f) : 
  (square f (x .+ a)) = ((square f x) .+ (((two f) .* (a .* x)) .+ (square f a))) := 
begin 
  unfold square, unfold two, 
  repeat {rw distrib_simp f _ _ _}, repeat {rw distrib_simp_alt f _ _ _}, 
  rw one_mul_simp f _, rw myfld.mul_comm a x, 
  repeat {rw myfld.add_assoc _ _ _}, 
end 

def quadratic_formula (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] (a b c : f) 
                                 (a_ne_zero : a ≠ myfld.zero) := 
      (.- b .+ (sqroot ((b .* b) .+ (.- ((four f) .* (a .* c))))))
      .*
      (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))


/- The proof of the correctness of the quadratic formula starts here. 
  The proof is split into a couple of different sections so that they can be reused when it comes time to 
     prove that negating the square root still gives a correct formula.-/ 

/- This first section does all the work between unfolding the formula and multiplying the square root by itself.-/ 
lemma quadratic_formula_sub_proof_a (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] (a b c sqrt : f) (a_ne_zero : a ≠ myfld.zero) : 
  (((a .* (((.- b) .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))) .* ((.- b) .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))))) .+ (a .* (((.- b) .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))) .* (sqrt .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero)))))) .+ ((a .* ((sqrt .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))) .* ((.- b) .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))))) .+ (a .* ((sqrt .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))) .* (sqrt .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))))))) .+ (((b .* ((.- b) .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero)))) .+ (b .* (sqrt .* (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))))) .+ c)
= 
c .+ ((myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero)) .* ((b .* (b .* (myfld.reciprocal (two f) (two_ne_zero f)))) .+ ((sqrt .* ((myfld.reciprocal (two f) (two_ne_zero f)) .* sqrt)) .+ ((.- b) .* b)))) := 
begin 
  /- First we can cancel inside some terms that have a * 1/2a.-/ 
  rw myfld.mul_comm _ (myfld.reciprocal ((two f) .* a) _), 
  repeat {rw <- myfld.mul_assoc (myfld.reciprocal ((two f) .* a) _) _ _}, 
  repeat {rw myfld.mul_assoc a (myfld.reciprocal ((two f) .* a) _) _}, 
  rw myfld.mul_comm sqrt (myfld.reciprocal ((two f) .* a) _), 
  rw <- myfld.mul_assoc (myfld.reciprocal ((two f) .* a) _) sqrt _, 
  rw myfld.mul_assoc a (myfld.reciprocal ((two f) .* a) _) _, 
  have cancel_a : (a .* (myfld.reciprocal ((two f) .* a) _)) = (myfld.reciprocal (two f) (two_ne_zero f)), 
    rw split_reciprocal f (two f) a _, 
    rw only_one_reciprocal f (two f) _ (two_ne_zero f), 
    rw myfld.mul_comm (myfld.reciprocal (two f) _) (myfld.reciprocal a _), 
    rw myfld.mul_assoc, rw myfld.mul_reciprocal a _, rw myfld.mul_comm _ _, 
    rw <- myfld.mul_one (myfld.reciprocal (two f) (two_ne_zero f)), 
  rw cancel_a, 

  /- There are two terms consisting of 1/2 * (-b) * 1/2a * sqrt (det) . 
  We can add these together into a single (-b) * 1/2a * sqrt (det) term.-/ 
  rw myfld.mul_assoc sqrt (myfld.reciprocal ((two f) .* a) _) (.- b), 
  rw myfld.mul_comm (sqrt .* (myfld.reciprocal ((two f) .* a) _)) (.- b), 
  rw myfld.mul_comm sqrt (myfld.reciprocal ((two f) .* a) _), 
  rw assoc_tree f _ ((myfld.reciprocal (two f) _) .* ((.- b) .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt))) ((myfld.reciprocal (two f) _) .* ((.- b) .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt))) _, 
  rw <- distrib_simp f (myfld.reciprocal (two f) _) _ _, 
  rw only_one_reciprocal f (two f) _ (two_ne_zero f), 
  rw add_two_halves f, rw one_mul f _, 

  /- (-b) * 1/2a * sqrt (det) cancels with b * 1/2a * sqrt (det) -/ 
  repeat {rw mul_negate f b _}, 
  rw myfld.add_comm (.- (b .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt))) (a .* (((myfld.reciprocal ((two f) .* a) _) .* sqrt) .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt))), 
  rw myfld.add_comm (b .* ((myfld.reciprocal ((two f) .* a) _) .* (.- b))) (b .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt)), 
  repeat {rw <- myfld.add_assoc}, 
  rw myfld.add_assoc (.- (b .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt))) (b .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt)) ((b .* ((myfld.reciprocal ((two f) .* a) _) .* (.- b))) .+ c), 
  rw myfld.add_comm (.- (b .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt))) (b .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt)), 
  rw myfld.add_negate (b .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt)), 
  rw myfld.add_comm myfld.zero _, rw zero_simp f _, 

  /- We can factorise out a common factor of 1/2a from everything except the +c at the end.-/ 
  rw myfld.mul_comm b ((myfld.reciprocal ((two f) .* a) _) .* (.- b)), 
  repeat {rw myfld.add_assoc _ _ _}, rw myfld.add_comm _ c, repeat {rw <- myfld.add_assoc _ _ _}, 
  rw myfld.mul_comm (myfld.reciprocal (two f) _) (.- (((myfld.reciprocal ((two f) .* a) _) .* (.- b)) .* b)), 
  rw <- mul_negate f ((myfld.reciprocal ((two f) .* a) _) .* (.- b)) b, 
  rw mul_negate_alt f (myfld.reciprocal ((two f) .* a) _) (.- b), 
  rw double_negative f b, 
  rw myfld.mul_comm a (((myfld.reciprocal ((two f) .* a) _) .* sqrt) .* ((myfld.reciprocal ((two f) .* a) _) .* sqrt)), 
  repeat {rw <- myfld.mul_assoc _ _ _}, 
  rw only_one_reciprocal f ((two f) .* a) _ (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero), 
  repeat {rw <- distrib_simp_alt f (myfld.reciprocal ((two f) .* a) _) _ _}, 

  /- There's one term left with a * 1/2a, which we cancel..-/ 
  rw myfld.mul_comm sqrt a, 
  rw myfld.mul_assoc (myfld.reciprocal ((two f) .* a) _) a _, 
  rw myfld.mul_comm (myfld.reciprocal ((two f) .* a) _) a, 
  rw cancel_a, clear cancel_a, 

  rw only_one_reciprocal f ((two f) .* a) _ (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero), 
  rw only_one_reciprocal f (two f) _ (two_ne_zero f), 
  rw mul_negate f b b, 
end 

/- This second section does all the work after the part that goes 
   (sqrt discriminant) * (sqrt discriminant) = discriminant.-/ 
lemma quadratic_formula_sub_proof_b (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] (a b c : f) (a_ne_zero : a ≠ myfld.zero) : 
  c .+ ((myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero)) .* ((b .* (b .* (myfld.reciprocal (two f) (two_ne_zero f)))) .+ ((((b .* b) .* (myfld.reciprocal (two f) (two_ne_zero f))) .+ ((.- ((four f) .* (a .* c))) .* (myfld.reciprocal (two f) (two_ne_zero f)))) .+ ((.- b) .* b))))
  = myfld.zero := 
begin 
  /- Two copies of b * b * 1/2 add together to give b * b...-/ 
  rw myfld.mul_assoc b b (myfld.reciprocal (two f) _), 
  repeat {rw <- myfld.add_assoc _ _ _}, 
  rw myfld.add_assoc ((b .* b) .* (myfld.reciprocal (two f) _)) ((b .* b) .* (myfld.reciprocal (two f) _)) _, 
  rw <- distrib_simp_alt f (b .* b) _ _, 
  rw add_two_halves f, rw <- myfld.mul_one (b .* b), 

  /- The b^2 that we just made cancels with the -b^2...-/ 
  rw myfld.add_comm (b .* b) (((.- ((four f) .* (a .* c))) .* (myfld.reciprocal (two f) _)) .+ ((.- b) .* b)), 
  rw <- myfld.add_assoc _ ((.- b) .* b) (b .* b), 
  rw mul_negate f b b, 
  rw myfld.add_comm (.- (b .* b)) (b .* b), 
  rw myfld.add_negate (b .* b), 
  rw <- myfld.add_zero ((.- ((four f) .* (a .* c))) .* (myfld.reciprocal (two f) _)), 

  /- We're now down to c + 1/2a * 4ac * 1/2, which is fairly obviously zero.-/ 
  /- All that's left to do is to simplify the second term.-/ 
  rw split_reciprocal f (two f) a _, rw myfld.mul_assoc (four f) a c, 
  rw myfld.mul_comm (four f) a, 
  rw mul_negate _ _, rw <- mul_negate_alt _ _, 
  rw assoc_tree_mul f _ _ _ _, rw myfld.mul_assoc (myfld.reciprocal a _) _ _, rw myfld.mul_assoc (myfld.reciprocal a _) a _, 
  rw myfld.mul_comm (myfld.reciprocal a _) a, rw myfld.mul_reciprocal a _, 
  rw one_mul f (four f), 
  rw myfld.mul_comm ((four f) .* c) (myfld.reciprocal (two f) _), 
  rw myfld.mul_assoc _ _ _, rw mul_two_reciprocals f (two f) (two f) _ _, 
  unfold four, rw two_plus_two f, 
  rw myfld.mul_assoc (myfld.reciprocal ((two f) .* (two f)) _) ((two f) .* (two f)) c, 
  rw myfld.mul_comm (myfld.reciprocal ((two f) .* (two f)) _) ((two f) .* (two f)), 
  rw myfld.mul_reciprocal ((two f) .* (two f)) _, rw one_mul f c, 
  exact myfld.add_negate c, 
end 

/- And so this brings the two halves together into a proof of the correctness of the formula.-/ 
lemma quadratic_formula_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] (a b c : f) (a_ne_zero : a ≠ myfld.zero) : 
    quadratic_subst f (quadratic_formula f a b c a_ne_zero) a b c = myfld.zero := 
begin 
  unfold quadratic_formula, unfold quadratic_subst, 
  rw distrib_simp f _ _ _, rw distrib_simp f _ _ _, repeat {rw distrib_simp_alt f _ _ _}, 

  rw quadratic_formula_sub_proof_a f a b c (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c))))) a_ne_zero, 

  /- One of our terms now has the square root of the discriminant multiplied by itself. 
  This, of course, gives us the discriminant.-/ 
  rw myfld.mul_comm (myfld.reciprocal (two f) _) (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c))))), 
  rw myfld.mul_assoc (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c))))) (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c))))) _, 
  rw fld_with_sqrt.sqrt_mul_sqrt ((b .* b) .+ (.- ((four f) .* (a .* c)))), 
  rw distrib_simp f _ _ _, 

  exact quadratic_formula_sub_proof_b f a b c a_ne_zero, 
end 

/- Of course, a given quadratic has two solutions...-/ 
def quadratic_formula_alt (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] (a b c : f) 
                                      (a_ne_zero : a ≠ myfld.zero) := 
      ((.- b) .+ (.- (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c))))))) .*
      (myfld.reciprocal ((two f) .* a) (mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero))

/- And both solutions are correct...-/ 
lemma quadratic_formula_alt_works (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] (a b c : f) (a_ne_zero : a ≠ myfld.zero) : 
    quadratic_subst f (quadratic_formula_alt f a b c a_ne_zero) a b c = myfld.zero := 
begin 
  unfold quadratic_formula_alt, unfold quadratic_subst, 
  rw distrib_simp f _ _ _, rw distrib_simp f _ _ _, repeat {rw distrib_simp_alt f _ _ _}, 

  rw quadratic_formula_sub_proof_a f a b c (.- (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c)))))) a_ne_zero, 

  /- One of our terms now has the negative of the square root of the discriminant multiplied by itself. 
  This, of course, gives us the discriminant.-/ 
  rw myfld.mul_comm (myfld.reciprocal (two f) _) (.- (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c)))))), 
  rw myfld.mul_assoc (.- (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c)))))) (.- (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c)))))) _, 
  rw negative_sqrt f ((b .* b) .+ (.- ((four f) .* (a .* c)))), 
  rw distrib_simp f _ _ _, 

  exact quadratic_formula_sub_proof_b f a b c a_ne_zero, 
end 
/- So both versions of the quadratic formula work properly.-/ 
/- However we have not proven that these are the only solutions.-/

/- OK: proof that no solutions to a quadratic exist besides the formula ones. -/ 
lemma quadratic_solution_unique (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] 
                                            (a b c x : f) (a_ne_zero : a ≠ myfld.zero) : 
          (x ≠ quadratic_formula f a b c a_ne_zero /\ x ≠ quadratic_formula_alt f a b c a_ne_zero) -> 
          quadratic_subst f x a b c ≠ myfld.zero := 
begin 
  intros not_formula h, 

  /- This will involve reducing the introduced formulae into a form that can be passed to 
        only_two_square_roots, which requires three formulae of the forms: 
        k ≠ sqrt (y)
        k ≠ - sqrt (y)
        k * k = y 
        So we first have to unfold the statement that x is not the solution to the quadratic formula 
        and reduce it to a form that looks like something ≠ ± (sqrt (something else)) . -/ 
  unfold quadratic_formula at not_formula, unfold quadratic_formula_alt at not_formula, 
  repeat {rw distrib_simp f _ _ _ at not_formula}, 
  repeat {rw myfld.add_comm ((.- b) .* (myfld.reciprocal ((two f) .* a) _)) _ at not_formula}, 
  rw mul_negate f _ _ at not_formula, 
  repeat {rw <- carry_term_across_ne f x _ (b .* (myfld.reciprocal ((two f) .* a) _)) at not_formula}, 
  cases not_formula with nfa nfb, 
  have two_a_ne_zero : ((two f) .* a) ≠ myfld.zero, 
    exact mul_nonzero f (two f) a (two_ne_zero f) a_ne_zero, 
  have nfa_tmp : (x .+ (b .* (myfld.reciprocal ((two f) .* a) _))) .* ((two f) .* a) ≠ ((sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c))))) .* (myfld.reciprocal ((two f) .* a) _)) .* ((two f) .* a) , 
    exact mul_both_sides_ne f _ _ ((two f) .* a) nfa two_a_ne_zero, 
  clear nfa, rename nfa_tmp nfa, 
  have nfb_tmp : (x .+ (b .* (myfld.reciprocal ((two f) .* a) _))) .* ((two f) .* a) ≠ ((.- (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c)))))) .* (myfld.reciprocal ((two f) .* a) _)) .* ((two f) .* a) , 
    exact mul_both_sides_ne f _ _ ((two f) .* a) nfb two_a_ne_zero, 
  clear nfb, rename nfb_tmp nfb, 
  rw distrib_simp f x (b .* (myfld.reciprocal ((two f) .* a) _)) _ at nfa nfb, 
  rw <- myfld.mul_assoc _ _ ((two f) .* a) at nfa nfb, rw <- myfld.mul_assoc _ _ ((two f) .* a) at nfa nfb, 
  repeat {rw myfld.mul_comm (myfld.reciprocal ((two f) .* a) _) ((two f) .* a) at nfa nfb}, 
  repeat {rw myfld.mul_reciprocal ((two f) .* a) _ at nfa nfb}, 
  rw <- myfld.mul_one b at nfa nfb, 
  rw <- myfld.mul_one (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c))))) at nfa, 
  rw <- myfld.mul_one (.- (sqroot  ((b .* b) .+ (.- ((four f) .* (a .* c)))))) at nfb, 
  clear two_a_ne_zero, 

  /- Next we have to unfold the actual quadratic and transform it into a similar form as the above, but with 
       square (something) ≠ (something else) . 
    This is pretty much just using the method of "completing the square" that we all learned at school.-/ 
  unfold quadratic_subst at h, 
  have h1 : ((a .* (x .* x)) .+ ((b .* x) .+ c)) .* (myfld.reciprocal a a_ne_zero)
                      = myfld.zero, 
    rw h, exact mul_zero f _, 
  clear h, rename h1 h, 
  rw distrib_simp f _ _ _ at h, 
  rw myfld.mul_comm (a .* (x .* x)) (myfld.reciprocal a a_ne_zero) at h, 
  rw myfld.mul_assoc (myfld.reciprocal a a_ne_zero) a _ at h, 
  rw myfld.mul_comm (myfld.reciprocal a a_ne_zero) a at h, rw myfld.mul_reciprocal a _ at h, 
  rw one_mul f _ at h, 
  rw distrib_simp f _ _ _ at h, rw myfld.add_assoc _ _ _ at h, 
  have tmp : ((b .* x) .* (myfld.reciprocal a a_ne_zero)) = 
             ((two f) .* ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* ((b .* x) .* (myfld.reciprocal a a_ne_zero)))), 
    have sub_tmp : ((two f) .* (myfld.reciprocal (two f) fld_not_char_two.not_char_two)) = myfld.one, 
      exact myfld.mul_reciprocal (two f) _, 
    rw myfld.mul_assoc (two f) (myfld.reciprocal (two f) _) _, rw sub_tmp, rw one_mul f _, 
  rw tmp at h, clear tmp, 
  rw <- myfld.mul_assoc b x _ at h, rw myfld.mul_comm x (myfld.reciprocal a a_ne_zero) at h, 
  rw myfld.mul_assoc _ _ x at h, rw myfld.mul_assoc _ _ x at h, rw myfld.mul_assoc _ _ x at h, 
  rw complete_the_square f x _ at h, 
  rw carry_term_across f _ _ (c .* (myfld.reciprocal a a_ne_zero)) at h, 
  rw simp_zero at h, 
  rw carry_term_across f _ _ (.- (square f ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (b .* (myfld.reciprocal a a_ne_zero))))) at h, 

  /- All the work that is at all interesting has been done above, the below is just a load of tedious rearranging 
       to make various expressions that anyone can see are equivalent visibly equal to the computer. 
     I wouldn't bother scrutinizing the below in detail unless you're having insomnia trouble.-/ 
  have h1 : (square f (x .+ ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (b .* (myfld.reciprocal a a_ne_zero))))) .* (square f ((two f) .* a)) = ((.- (c .* (myfld.reciprocal a a_ne_zero))) .+ (.- (.- (square f ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (b .* (myfld.reciprocal a a_ne_zero))))))) .* (square f ((two f) .* a)) , 
    have h_tmp : (square f (x .+ ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (b .* (myfld.reciprocal a a_ne_zero))))) .* (square f ((two f) .* a)) = (square f (x .+ ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (b .* (myfld.reciprocal a a_ne_zero))))) .* (square f ((two f) .* a)) , 
      refl, 
    rw h at h_tmp {occs := occurrences.pos [2]}, exact h_tmp, 
  clear h, rename h1 h, 
  rw multiply_two_squares f _ _ at h, 
  rw distrib_simp f _ _ _ at h, 
  rw myfld.mul_assoc ((myfld.reciprocal (two f) fld_not_char_two.not_char_two) .* (b .* (myfld.reciprocal a a_ne_zero))) (two f) a at h, 
  rw myfld.mul_comm (myfld.reciprocal (two f) fld_not_char_two.not_char_two) _ at h, 
  rw <- myfld.mul_assoc _ (myfld.reciprocal (two f) fld_not_char_two.not_char_two) (two f) at h, 
  rw myfld.mul_comm (myfld.reciprocal (two f) fld_not_char_two.not_char_two) (two f) at h, 
  rw myfld.mul_reciprocal _ _ at h, rw simp_mul_one f _ at h, 
  rw <- myfld.mul_assoc _ (myfld.reciprocal a a_ne_zero) a at h, 
  rw myfld.mul_comm (myfld.reciprocal a a_ne_zero) a at h, 
  rw myfld.mul_reciprocal _ _ at h, rw simp_mul_one f _ at h, 

  rw double_negative f _ at h, rw distrib_simp f _ _ _ at h, rw multiply_two_squares f _ _ at h, 
  have tmp : (square f ((two f) .* a)) = a .* ((four f) .* a) , 
    unfold square, unfold four, rw two_plus_two f, rw <- myfld.mul_assoc (two f) (two f) a, 
    have tmp_tmp : a .* ((two f) .* ((two f) .* a)) = a .* ((two f) .* (a .* (two f))) , 
      rw myfld.mul_comm (two f) a, 
    rw tmp_tmp, rw myfld.mul_comm (two f) a, repeat {rw myfld.mul_assoc _ _ _}, 
  rw tmp at h, clear tmp, 
  rw mul_negate at h, 
  rw myfld.mul_assoc (c .* (myfld.reciprocal a a_ne_zero)) a _ at h, 
  rw <- myfld.mul_assoc c _ a at h, rw myfld.mul_comm (myfld.reciprocal a _) a at h, 
  rw myfld.mul_reciprocal a _ at h, rw simp_mul_one f _ at h, 
  rw <- myfld.mul_assoc _ (myfld.reciprocal (two f) _) _ at h, 
  rw myfld.mul_assoc (myfld.reciprocal (two f) _) (two f) a at h, 
  rw myfld.mul_comm (myfld.reciprocal (two f) _) (two f) at h, 
  rw myfld.mul_reciprocal (two f) _ at h, rw one_mul f _ at h, 
  rw <- myfld.mul_assoc b _ a at h, rw myfld.mul_comm (myfld.reciprocal a a_ne_zero) a at h, 
  rw myfld.mul_reciprocal a a_ne_zero at h, rw simp_mul_one f b at h, 
  have tmp : (square f b) = b .* b, unfold square, 
  rw tmp at h, clear tmp, 
  rw myfld.add_comm _ (b .* b) at h, 
  rw myfld.mul_assoc c (four f) a at h, rw myfld.mul_comm c (four f) at h, 
  rw <- myfld.mul_assoc (four f) c a at h, rw myfld.mul_comm c a at h, 

  /- Having finally finished rearranging, the problem has been reduced to the question of whether 
     more than two square roots of the same number can exist. 
     They can't.-/ 
  exact only_two_square_roots f ((x .* ((two f) .* a)) .+ b) ((b .* b) .+ (.- ((four f) .* (a .* c)))) nfa nfb h, 
end 

/- QED.-/ 

lemma quadratic_factorize (f : Type) [myfld f] [fld_with_sqrt f] [fld_not_char_two f] (b c x : f)
    : (x .+ .- (quadratic_formula f myfld.one b c myfld.zero_distinct_one)) .* 
        (x .+ .- (quadratic_formula_alt f myfld.one b c myfld.zero_distinct_one))
    =
    (quadratic_subst f x myfld.one b c) :=
begin
  rw distrib_simp, rw distrib_simp_alt, rw distrib_simp_alt,
  repeat {rw mul_negate, rw mul_negate_alt_simp}, rw double_negative,
  rw myfld.mul_comm (quadratic_formula f myfld.one b c _) x,
  repeat {rw <- myfld.add_assoc}, rw myfld.add_assoc (.- _) (.- _) _, rw <- add_negate,
  rw <- distrib_simp_alt,
  have tmp : (quadratic_formula f myfld.one b c myfld.zero_distinct_one) .+ 
             (quadratic_formula_alt f myfld.one b c myfld.zero_distinct_one) = .- b,
    unfold quadratic_formula, unfold quadratic_formula_alt,
    rw <- distrib_simp, repeat {rw <- myfld.add_assoc},
    rw reciprocal_rewrite f _ _ (simp_mul_one f _) _,
    rw one_mul_simp f,
    rw myfld.add_comm _ (.- sqroot _), rw myfld.add_assoc (sqroot _) (.- sqroot _) _,
    rw myfld.add_negate, rw simp_zero,
    rw distrib_simp, rw <- distrib_simp_alt, rw add_two_halves, rw simp_mul_one,
  rw myfld.add_comm at tmp,
  rw tmp, clear tmp,
  have clear_term : ∀ (a b x : f), a = b -> (x .+ a) = (x .+ b), 
    intros a b x h, rw h,
  unfold quadratic_subst, rw one_mul_simp, apply clear_term,
  rw mul_negate_alt_simp, rw double_negative, rw myfld.mul_comm x b, apply clear_term,
  clear clear_term,
  unfold quadratic_formula, unfold quadratic_formula_alt,
  repeat {rw <- myfld.mul_assoc}, rw myfld.mul_comm (myfld.reciprocal _ _) _,
  repeat {rw myfld.mul_assoc},
  rw difference_of_squares, 
  rw sqrt_squared, unfold square,
  rw mul_negate, rw mul_negate_alt_simp, rw double_negative, rw add_negate,
  rw myfld.add_assoc, rw myfld.add_negate, rw simp_zero, rw double_negative,
  rw <- myfld.mul_assoc, 
  rw reciprocal_rewrite f _ _ (simp_mul_one f _) _,
  rw mul_two_reciprocals, rw myfld.mul_comm _ c,
  rw <- myfld.mul_assoc c _ _, rw simp_mul_one,
  unfold four, rw two_plus_two, rw myfld.mul_reciprocal, rw simp_mul_one,
end
