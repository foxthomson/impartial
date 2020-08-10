import set_theory.ordinal
import impartial
import data.set

universes u v

local infix ` ≈ ` := pgame.equiv

/-- The defineition of nim, nim O is the game where each player can move to nim O' where O' < O 
    If O is finite then this game can be veiwed as a pile of stones where each player can take a
	positie number of stones from it on their turn -/
def nim : ordinal → pgame
| O₁ := ⟨ { O₂ : ordinal // O₂ < O₁ },
					{ O₂ : ordinal // O₂ < O₁ },
					λ O₂, have hwf : ↑O₂ < O₁, from O₂.prop, nim O₂,
					λ O₂, have hwf : ↑O₂ < O₁, from O₂.prop, nim O₂ ⟩
using_well_founded {dec_tac := tactic.assumption}

@[simp] lemma nim_def (O : ordinal) : nim O = pgame.mk { O₂ : ordinal // O₂ < O } 
					{ O₂ : ordinal // O₂ < O }
					(λ O₂, nim O₂)
					(λ O₂, nim O₂) :=
by rw nim

@[instance] lemma nim_impartial : ∀ (O : ordinal), pgame.impartial (nim O)
| O := 
begin
	rw pgame.impartial_def,
	rw nim_def,
	rw pgame.neg_def,
	split,
	split,
	{ rw pgame.le_def,
	  split,
		{ intro i,
			left,
		  use i,
			let hwf := i.prop,
			exact (@pgame.impartial_neg_equiv_self (nim ↑i) (nim_impartial ↑i)).1 },
		{ intro j,
			right,
			use j,
			let hwf := j.prop,
			exact (@pgame.impartial_neg_equiv_self (nim ↑j) (nim_impartial ↑j)).1 } },
	{ rw pgame.le_def,
		split,
		{ intro i,
			left,
			use i,
			let hwf := i.prop,
			exact (@pgame.impartial_neg_equiv_self (nim ↑i) (nim_impartial ↑i)).2 },
		{ intro j,
			right,
			use j,
			let hwf := j.prop,
			exact (@pgame.impartial_neg_equiv_self (nim ↑j) (nim_impartial ↑j)).2 } },
	split,
	{ intro i,
		rw pgame.move_left_mk,
		let hwf := i.prop,
		exact nim_impartial ↑i },
	{ intro j,
		rw pgame.move_right_mk,
		let hwf := j.prop,
		exact nim_impartial ↑j }
end
using_well_founded {dec_tac := tactic.assumption}

/-- This definition will be used in the proof of the Sprague-Grundy theorem. It takes a function
	from some type to ordinals and returns a nonempty set of ordinals with empty intersection with
	the image of the function. It is guarantied that the smallest ordinal not in the image will be
	in the set, i.e. we can use this to find the mex -/
def nonmoves {α : Type _} (M : α → ordinal.{u}) : set ordinal.{u+1} := { O : ordinal | ¬ ∃ a : α, ordinal.lift.{u (u+1)} (M a) = O }

lemma nonmoves_nonempty {α : Type _} (M : α → ordinal.{u}) : ∃ O : ordinal, O ∈ nonmoves M :=
begin
	have h : ¬ ∃ a, ordinal.lift.{u (u+1)} (M a) = ordinal.lift.principal_seg.{u (u+1)}.top,
	rintro ⟨ a, ha ⟩,
	have down := ordinal.lift.principal_seg.{u (u+1)}.down (ordinal.lift.{u (u+1)} (M a)),
	have h' : ∃ (b : ordinal), ordinal.lift.principal_seg.{u (u+1)} b = (ordinal.lift.{u (u+1)} (M a)),
		use M a,
		rw ordinal.lift.principal_seg_coe,
	have hcontra := down.2 h',
	have h := (lt_iff_le_and_ne.1 hcontra).2,
	contradiction,
	use ordinal.lift.principal_seg.{u (u+1)}.top
end

/-- This is an attempt to state the Sprague-Grundy theorem -/
/-
theorem Sprague_Grundy : ∀ (G : pgame.{u+2}) [G.impartial], inhabited { O : ordinal.{u+1} // G ≈ nim O }
| G := 
begin
	classical,
	introI,
	fconstructor,
	fconstructor,
	

	classical,
	introI,
	let M := λ i, (Sprague_Grundy (G.move_left i)).default.val,
	fconstructor,
	fconstructor,
	have S := nonmoves M,
	apply ordinal.omin,
	exact nonmoves_nonempty M,
	-- exact ordinal.omin.{u+1} (nonmoves M) (nonmoves_nonempty M)
	sorry,
end
-/