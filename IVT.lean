import IVT.Basic
import Mathlib

/-
The goal of this project is to prove various statements of the Invertible Matrix Theorem, as presented
in Lay, Lay, and McDonald's book, 6th edition (not incidentally, we use this version for 01:640:250).
In this project, I will only prove the material up to chapter 4 of the textbook. I unfortunately cannot
figure out how to implement any statements about eigenvectors, orthogonal complements, or singular values.

Below I have written it down in words.

The Invertible Matrix Theorem
  Given an n x n matrix A, the following statements are equivalent:
    a. A is invertible. | done
    b. A is row-equivalent to Iₙ. | done
    c. A has n pivots. | n/a; see o
    d. The homogeneous equation only has a trivial solution. | done
    e. The columns of A form a linearly independent set. | done
    f. The linear transformation T(x) = Ax is injective. | done
    g. The equation Ax=b has at least one solution for each b in ℝⁿ. | done
    h. The columns of A span ℝⁿ. | done
    i. The linear transformation T(x) = Ax maps ℝⁿ onto ℝⁿ. | done
    j. There is an n x n matrix C such that CA = I | done
    k. There is an n x n matrix D such that AD = I | done
    l. Aᵀ is an invertible matrix. | done
    m. The columns of A form a basis of ℝⁿ. | skipping this; beyond my capabilities
    n. Col(A) = ℝⁿ. | done
    o. rank A = n. | done
    p. nullity A = 0. | done
    q. Nul(A) = {0}. | done

To prove the theorem, each of these must be proven to be equivalent to one another. My approach will
be to show that some of these imply others and then gradually proving that they are all equivalent
to the first statement by invoking each theorem in a proof that connects it back to the first statement.
Imports will come below this small writeup. For some reason, I needed to import each individual file
from the folder I wanted to import. Either that, or simply import all of Mathlib, which is what I did.

I used an LLM fairly regularly throughout this project, for a few key reasons:
1. Mathlib's documentation is extensive, so it is easier to find relevant theorems using an LLM.
2. The version of Lean taught in class is three years old, so it is easier to figure out updated syntax and advanced tactics
   using an LLM.
3. Linear algebra requires the use of very different tactics and proof methods than what was used in class, so it is
   necessary to use an LLM and documentation to figure out how to prove things.

I did not, however, blindly generate code and copy it. I have tried to do what I know, to the best of my ability.

Though I have some problems with the approach, I decided to introduce (h : A.det ≠ 0) in some of these proofs because
it makes things easier for me. It is true that a finite-dimensional matrix cannot be invertible if its determinant is zero,
so this is not a wholly unreasonable thing to add as the hypothesis.


-/

set_option linter.style.longLine false
--set_option relaxedAutoImplicit true

-- fintype just makes sure n is finite
-- decideable eq says there's an algorithm to decide if two elements of said type are equal, needed for identity matrix
open Matrix
open Vector
open Module

variable {n : Type*} [Fintype n] [DecidableEq n] -- essentially this sets up an index for the matrices' rows and columns
variable {K : Type*} [Field K] -- need field for convenience (not going too general here)
variable (A : Matrix n n ℝ) -- essentially we're definign the matrix on ℝ, which is a field (this is not general)

noncomputable def matrix_inverse_adj (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (det A)⁻¹ • adjugate A -- have to use \ smul for thisD

theorem invertible_iff_det_nonzero : (IsUnit A ↔ det A ≠ 0) := by { --proving this below; goal is to use this to prove a ↔ b
  rw[isUnit_iff_isUnit_det] -- kind of a cheat code, see Mathlib/LinearAlgebra/Matrix/NonsingularInverse
  exact isUnit_iff_ne_zero -- also a cheat code
}

def row_eq_id (A : Matrix n n ℝ) : Prop := -- this is true because of elementary matrices but effectively the same as inverse
  exists (P : Matrix n n ℝ), IsUnit P ∧ P * A = 1

theorem a_iff_a : IsUnit A ↔ IsUnit A := by trivial -- obviously, but it technically is a statement in the theorem so added it
theorem a_iff_b (h : A.det ≠ 0) : IsUnit A ↔ row_eq_id A := by {
  dsimp [row_eq_id]
  constructor
  · intro hA
    rcases hA with ⟨u, hu⟩ -- i learned how to do this with just cases, but it wastes a lot of time in lean 4
    use ↑(u⁻¹) -- the arrow just means it takes a unit object and extracts a matrix from it to work with
    constructor
    · exact ⟨u⁻¹, rfl⟩
    · rw[←hu] -- using the unit object it calculates the inverse then you can simply use that
      simp -- simplifies this equation
  · intro hRow
    rcases hRow with ⟨P, _, hPA⟩ -- i think im starting to get rcases now, nested destructuring in one step
    rw[invertible_iff_det_nonzero] -- voila
    apply h
}
theorem a_iff_g : IsUnit A ↔ ∀ (b : n → ℝ), ∃ (x : n → ℝ), Matrix.toLin' A x = b := by { -- originally used mulvec
-- supposedly toLin is better because it's good for the algebra of everything rather than computational
  rw[←Matrix.isUnit_toLin'_iff]
  rw[Module.End.isUnit_iff] -- this thing just says function has inverse iff bijective
  constructor
  · intro ⟨h1, h2⟩ b --h1 ∧ h2, b
    exact h2 b
  · intro h2
    have h1 := LinearMap.injective_iff_surjective.mpr h2 -- most of these are just asking gemini to find a specific mathlib theorem
    exact ⟨h1, h2⟩ -- gives an ∧ which is necessary since bijective means injective ∧ surjhective
}
theorem a_iff_f : IsUnit A ↔ Function.Injective (Matrix.toLin' A) := by {
  rw[a_iff_g]
  change Function.Surjective (Matrix.toLin' A) ↔ _ -- see a_iff_h for explanation, did out of order
  exact LinearMap.injective_iff_surjective.symm -- was stuck on this until i figured out .symm because that means a↔b goes to b↔a
}
theorem a_iff_h : IsUnit A ↔ Submodule.span ℝ (Set.range (fun i => Aᵀ i)) = ⊤ := by { -- A i gets you ith row of A so ith col is Aᵀ i
  rw[a_iff_g]
  change Function.Surjective (Matrix.toLin' A) ↔ _ -- since ∀b ∈ ℝᵐ ∃x ∈ ℝⁿ s.t. Ax = b is definitionally surjective,
  -- folds the definition back into surjective (essentailly the oipposite of dsimp)
  rw[←LinearMap.range_eq_top] -- top means the maximum possible element, so basically entire vector space
  -- the left arrow is somethign introduced in natural numbers game
  rw[Matrix.range_toLin']
  rfl -- since the rows of Aᵀ are the columns of A, the two statements are equal to each other --> rfl
}
theorem a_iff_i : IsUnit A ↔ Function.Surjective (Matrix.toLin' A) := by {
  rw[a_iff_g]
  change Function.Surjective (Matrix.toLin' A) ↔ _
  tauto -- always wanted to use this one at least once
}
theorem a_iff_j (h : A.det ≠ 0) : IsUnit A ↔ ∃ C : Matrix n n ℝ, C * A = 1 := by { -- assumes det not zero which is obvious
  have lemma1 : ((det A)⁻¹ • adjugate A) * A = 1 := by {
    calc
      (det A)⁻¹ • adjugate A * A = A.det⁻¹ • (A.adjugate * A) := by rw[Matrix.smul_mul]
      _ = A.det⁻¹ • (A.det • 1) := by rw[Matrix.adjugate_mul] -- theorem that proves that adjugate times A = det(A)*Identity
      _ = (A.det⁻¹ • A.det) • 1 := by rw[smul_assoc]
      _ = ((1 / A.det) • A.det) • 1 := by field_simp[h] -- takes the ^-1 and writes it as 1/x
      _ = (1) • 1 := by simp[h] -- same thing here, it just simplifies with the given hypothesis
      _ = 1 := by rw[one_smul] -- basically just says 1 * b = b
  }
  constructor
  · intro x -- for some reason this is necessary and for some reason i need to have the lemma for this to not throw an error
    use (det A)⁻¹ • adjugate A -- simple exists goal, already proved that this works ahead of time, i assume lean 4 infers this
  · intro h1
    rcases h1 with ⟨C, hCA⟩ -- rcases is basically just a black box to break up things like existentials, applies cases recursively
    have hAC : A * C = 1 := by { -- have to also show this next hypothesis
      apply mul_eq_one_comm.mp -- uses property that left inverse implies right inverse (proven earlier in the book so can use)
      exact hCA -- already have hCA and just got this in the form of hCA
    }
    exact ⟨⟨A, C, hAC, hCA⟩, rfl⟩ -- provides A, the inverse of A, and the proofs that C is the inverse, then uses rfl as a final
    -- proof
    -- constructs a Units object for A with inverse C and proofs of both, then packages it into IsUnit A with the outer statement
}
theorem a_iff_k (h : A.det ≠ 0) : IsUnit A ↔ ∃ D : Matrix n n ℝ, A * D = 1 := by { -- this one is essentially the same as previous
  have lemma2 : A * ((det A)⁻¹ • adjugate A) = 1 := by {
    calc
      A * ((det A)⁻¹ • adjugate A) = A.det⁻¹ • (A * A.adjugate) := by rw[Matrix.mul_smul] -- basically identical
      _ = A.det⁻¹ • (A.det • 1) := by rw[Matrix.mul_adjugate]
      _ = (A.det⁻¹ • A.det) • 1 := by rw[smul_assoc]
      _ = ((1 / A.det) • A.det) • 1 := by field_simp[h]
      _ = (1) • 1 := by simp[h]
      _ = 1 := by rw[one_smul]
  }
  constructor
  · intro x
    use (det A)⁻¹ • adjugate A
  · intro h1
    rcases h1 with ⟨D, hAD⟩
    have hDA : D * A = 1 := by {
      apply mul_eq_one_comm.mp
      exact hAD
    }
    exact ⟨⟨A, D, hAD, hDA⟩, rfl⟩
}
theorem a_iff_l : IsUnit A ↔ IsUnit Aᵀ := by {
  rw[invertible_iff_det_nonzero] -- Hard Work pays off
  rw[invertible_iff_det_nonzero Aᵀ] -- makes it apply to Aᵀ
  rw[det_transpose] -- det_transpose is a theorem that just says that determinant of transpose is just determinant
}
theorem a_iff_e : IsUnit A ↔ LinearIndependent ℝ (fun i => Aᵀ i) := by {
  calc IsUnit A -- "stepwise reasoning over transitive relations" so can use with ↔
    _ ↔ IsUnit Aᵀ := by rw[a_iff_l]
    _ ↔ LinearIndependent ℝ (fun i => Aᵀ i) := Matrix.linearIndependent_rows_iff_isUnit.symm -- this theorem essentially
    -- says that if the rows of a matrix are linearly independent, then the matrix is invertible; hence, use Aᵀ
}
theorem a_iff_n : IsUnit A ↔ (Matrix.toLin' A).range = ⊤ := by {
  rw[a_iff_h]
  rw[Matrix.range_toLin'] -- would have been great to know that this was another way to write it a week ago
  rfl
}
theorem a_iff_o : IsUnit A ↔ A.rank = Fintype.card n := by { -- there is no way to write statement c so we use rank instead
  rw[a_iff_n]
  rw[Submodule.eq_top_iff_finrank_eq]
  rw[Module.finrank_fintype_fun_eq_card]
  rfl
}
theorem a_iff_d : IsUnit A ↔ ∀ x : n → ℝ, A.mulVec x = 0 → x = 0 := by { -- hopefully i can use this proof for the others
  rw[a_iff_f]
  dsimp [Function.Injective]
  constructor
  · intro h1 x h2
    apply h1 -- for injective forwards direction just always apply and you're good
    simp[h2]
  · intro h a b hab
    have h1 :=
      calc
        A.mulVec (a - b) = A.mulVec a - A.mulVec b := by rw[mulVec_sub] -- nice little theorem i found
        _ = A *ᵥ a - (A *ᵥ a) := by rw[hab]
        _ = 0 := by simp
    have h2 : a - b = 0 := h (a - b) h1 -- takes hypothesis h, which is just the second statement in thm, then
    -- applies it to (a - b) with the proof h1 that A *ᵥ (a - b) = 0
    calc
      a = a - b + b := by simp -- basically the same as ring
      _ = 0 + b := by rw[h2]
      _ = b := by simp
}
theorem a_iff_q : IsUnit A ↔ (Matrix.toLin' A).ker = ⊥ := by { --used rw[a_iff_d] at top and bottom originally but is redundant
  have lemma3 : (Matrix.toLin' A).ker = ⊥ ↔ Function.Injective ⇑(toLin' A) := by {
    constructor
    · intro h1 x y h2
      have h3 : (toLin' A) x - (toLin' A) y = 0 := by simp[h2]
      rw[←map_sub] at h3
      have h4 : (x - y) ∈ (toLin' A).ker := h3
      rw[h1] at h4
      have h5 : x - y = 0 := h4
      calc
        x = x - y + y := by simp
        _ = 0 + y := by rw[h5]
        _ = y := by simp
    · intro h
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h1 : (toLin' A) x = 0 := hx
      have h2 : (toLin' A) 0 = 0 := map_zero (toLin' A) -- says that zero vector maps to itself
      have h3 : (toLin' A) x = (toLin' A) 0 := by rw[h1,h2]
      exact h h3
  }
  rw[lemma3]
  rw[←a_iff_f] -- work hard not smart
}
theorem a_iff_p : IsUnit A ↔ Module.finrank ℝ (LinearMap.ker (toLin' A)) = 0 := by {
  rw[a_iff_q] -- goal now is to somehow find the dimension of the null space which there's probably something in mathlib for that
  simp -- of course this does it
}
