inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:51 := fml.not

inductive prf : fml → Type
| axk (p q) : prf (p →' q →' p)
| axs (p q r) : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX (p q) : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

open prf

theorem not_not_p_of_p (p q : fml) : prf (p →' (¬' (¬' p))) :=
mp (mp (mp (axk (¬' p) (¬' p)) 
           (axk (¬' p →' ¬' p →' ¬' p) (¬' ¬' ¬' p))
       )
       (mp (mp (mp (mp (mp (axk (¬' ¬' ¬' p) (¬' ¬' ¬' p)) 
                           (mp (axk (¬' ¬' ¬' p) (¬' ¬' ¬' p →' ¬' ¬' ¬' p))
                               (axs (¬' ¬' ¬' p) (¬' ¬' ¬' p →' ¬' ¬' ¬' p) (¬' ¬' ¬' p))
                           )
                       )
                       (mp (mp (axk (¬' ¬' ¬' p) (¬' ¬' (¬' p →' ¬' p →' ¬' p))) 
                               (axk (¬' ¬' ¬' p →' (¬' ¬' (¬' p →' ¬' p →' ¬' p)) →' ¬' ¬' ¬' p) (¬' ¬' ¬' p))
                           ) 
                           (axs (¬' ¬' ¬' p) (¬' ¬' ¬' p) (¬' ¬' (¬' p →' ¬' p →' ¬' p) →' ¬' ¬' ¬' p))
                       )
                   ) 
                   (mp (mp (axX (¬' ¬' p) ¬' (¬' p →' ¬' p →' ¬' p)) 
                           (axk ((¬' ¬' (¬' p →' ¬' p →' ¬' p) →' ¬' ¬' ¬' p) →' ¬' ¬' p →' ¬' (¬' p →' ¬' p →' ¬' p)) (¬' ¬' ¬' p))
                       ) 
                       (axs (¬' ¬' ¬' p) (¬' ¬' (¬' p →' ¬' p →' ¬' p) →' ¬' ¬' ¬' p) (¬' ¬' p →' ¬' (¬' p →' ¬' p →' ¬' p)))
                   )
               ) 
               (mp (mp (axX (¬' p →' ¬' p →' ¬' p) (¬' p)) 
                       (axk ((¬' (¬' p) →' ¬' (¬' p →' ¬' p →' ¬' p)) →' (¬' p →' ¬' p →' ¬' p) →' ¬' p) (¬' ¬' ¬' p))
                   ) 
                   (axs (¬' ¬' ¬' p) (¬' ¬' p →' ¬' (¬' p →' ¬' p →' ¬' p)) ((¬' p →' ¬' p →' ¬' p) →' ¬' p))
               )
           ) 
           (axs (¬' ¬' ¬' p) (¬' p →' ¬' p →' ¬' p) (¬' p))
       )
   ) 
   (axX p (¬' ¬' p))
