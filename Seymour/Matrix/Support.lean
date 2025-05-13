import Seymour.Basic.Fin


variable {X Y R : Type} [Zero R] [DecidableEq R]

@[simp]
def Matrix.support (A : Matrix X Y R) : Matrix X Y Z2 :=
  Matrix.of (if A · · = 0 then 0 else 1)

lemma Matrix.support_transpose (A : Matrix X Y R) :
    A.support.transpose = A.transpose.support :=
  rfl

lemma Matrix.support_submatrix {X' Y' : Type} (A : Matrix X Y R) (f : X' → X) (g : Y' → Y) :
    A.support.submatrix f g = (A.submatrix f g).support :=
  rfl

omit R

lemma Matrix.support_Z2 {X Y : Type} (A : Matrix X Y Z2) : A.support = A := by
  aesop
