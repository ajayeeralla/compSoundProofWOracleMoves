
Definition x2 :=  (f
          [pk (N 1); pk (N 2);
          if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
            (enc (N 3, pk (N 1)) (m x1) (sr 1))
            (if_then_else_M (EQ_M (to x1) (i 2))
               (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) 
                  (pk (N 1)) (sr 2)) O)]).
Definition x3 := (f
         [pk (N 1); pk (N 2);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (enc (N 3, pk (N 1)) (m x1) (sr 1))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) 
                 (pk (N 1)) (sr 2)) O);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
              (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (m x1) (sr 3))
              (if_then_else_M (EQ_M (to x2) (i 2))
                 (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) 
                    (pk (N 1)) (sr 4)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                 (enc (N 3, pk (N 1)) (m x2) (sr 5))
                 (if_then_else_M
                    (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4))
                    acc O)) O)]).
Definition x4 :=  (f
         [pk (N 1); pk (N 2);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (enc (N 3, pk (N 1)) (m x1) (sr 1))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) 
                 (pk (N 1)) (sr 2)) O);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
              (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (m x1) (sr 3))
              (if_then_else_M (EQ_M (to x2) (i 2))
                 (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) 
                    (pk (N 1)) (sr 4)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                 (enc (N 3, pk (N 1)) (m x2) (sr 5))
                 (if_then_else_M
                    (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4))
                    acc O)) O);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
              (if_then_else_M (EQ_M (to x3) (i 2))
                 (enc (pi1 (dec x3 (sk (N 2))), (N 4, pk (N 2))) 
                    (pk (N 1)) (sr 6)) O)
              (if_then_else_M (EQ_M (to x2) (i 2))
                 (if_then_else_M
                    ((EQ_M (to x3) (i 1)) &
                     (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                    (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 7))
                    (if_then_else_M
                       (EQ_M (to x3) (i 2)) &
                       (EQ_M (dec x3 (sk (N 2))) (N 4)) acc O)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                 (if_then_else_M
                    ((EQ_M (to x3) (i 1)) &
                     (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                    (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 7))
                    (if_then_else_M
                       (EQ_M (to x3) (i 2)) &
                       (EQ_M (dec x3 (sk (N 2))) (N 4)) acc O))
                 (if_then_else_M
                    (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4))
                    (if_then_else_M
                       (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                       (enc (N 3, pk (N 1)) (m x1) (sr 8)) O) O)) O)]).
Definition x5 :=  (f
         [pk (N 1); pk (N 2); t12; t13;
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
              (if_then_else_M (EQ_M (to x3) (i 2))
                 (enc (pi1 (dec x3 (sk (N 2))), (N 4, pk (N 2))) 
                    (pk (N 1)) (sr 6)) O)
              (if_then_else_M (EQ_M (to x2) (i 2))
                 (if_then_else_M
                    ((EQ_M (to x3) (i 1)) &
                     (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                    (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 7))
                    (if_then_else_M
                       (EQ_M (to x3) (i 2)) &
                       (EQ_M (dec x3 (sk (N 2))) (N 4)) acc O)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                 (if_then_else_M
                    ((EQ_M (to x3) (i 1)) &
                     (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                    (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 7))
                    (if_then_else_M
                       (EQ_M (to x3) (i 2)) &
                       (EQ_M (dec x3 (sk (N 2))) (N 4)) acc O))
                 (if_then_else_M
                    (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4))
                    (if_then_else_M
                       (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                       (enc (N 3, pk (N 1)) (m x1) (sr 8)) O) O)) O);
         if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
           (if_then_else_M
              ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
              (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
              (if_then_else_M (EQ_M (to x3) (i 2))
                 (if_then_else_M
                    (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4))
                    acc O) O)
              (if_then_else_M (EQ_M (to x2) (i 2))
                 (if_then_else_M
                    ((EQ_M (to x3) (i 1)) &
                     (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                    (if_then_else_M
                       (EQ_M (to x4) (i 2)) &
                       (EQ_M (dec x4 (sk (N 2))) (N 4)) acc O)
                    (if_then_else_M
                       (EQ_M (to x3) (i 2)) &
                       (EQ_M (dec x3 (sk (N 2))) (N 4))
                       (if_then_else_M
                          ((EQ_M (to x4) (i 1)) &
                           (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                          (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                          (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 9))
                          O) O)) O))
           (if_then_else_M (EQ_M (to x1) (i 2))
              (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                 (if_then_else_M
                    ((EQ_M (to x3) (i 1)) &
                     (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                    (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                    (if_then_else_M
                       (EQ_M (to x4) (i 2)) &
                       (EQ_M (dec x4 (sk (N 2))) (N 4)) acc O)
                    (if_then_else_M
                       (EQ_M (to x3) (i 2)) &
                       (EQ_M (dec x3 (sk (N 2))) (N 4))
                       (if_then_else_M
                          ((EQ_M (to x4) (i 1)) &
                           (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                          (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                          (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 9))
                          O) O))
                 (if_then_else_M
                    (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4))
                    (if_then_else_M
                       (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                       (if_then_else_M
                          ((EQ_M (to x4) (i 1)) &
                           (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                          (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                          (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 9))
                          O) O) O)) O)]).
Definition t12 := (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
          (enc (N 3, pk (N 1)) (m x1) (sr 1))
          (if_then_else_M (EQ_M (to x1) (i 2))
             (enc (pi1 (dec x1 (sk (N 2))), (N 4, pk (N 2))) 
                (pk (N 1)) (sr 2)) O)).
Definition t13 :=    (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
            (enc (pi1 (pi2 (dec x2 (sk (N 1))))) (m x1) (sr 3))
            (if_then_else_M (EQ_M (to x2) (i 2))
               (enc (pi1 (dec x2 (sk (N 2))), (N 4, pk (N 2))) 
                  (pk (N 1)) (sr 4)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (enc (N 3, pk (N 1)) (m x2) (sr 5))
               (if_then_else_M
                  (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4)) acc
                  O)) O)).
Definition t14 :=(if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
            (if_then_else_M (EQ_M (to x3) (i 2))
               (enc (pi1 (dec x3 (sk (N 2))), (N 4, pk (N 2))) 
                  (pk (N 1)) (sr 6)) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M
                  ((EQ_M (to x3) (i 1)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                  (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 7))
                  (if_then_else_M
                     (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4))
                     acc O)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M
                  ((EQ_M (to x3) (i 1)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                  (enc (pi1 (pi2 (dec x3 (sk (N 1))))) (m x1) (sr 7))
                  (if_then_else_M
                     (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4))
                     acc O))
               (if_then_else_M
                  (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4))
                  (if_then_else_M (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                     (enc (N 3, pk (N 1)) (m x1) (sr 8)) O) O)) O)).
Definition t15 := (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
            (if_then_else_M (EQ_M (to x3) (i 2))
               (if_then_else_M
                  (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4)) acc
                  O) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M
                  ((EQ_M (to x3) (i 1)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                  (if_then_else_M
                     (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4))
                     acc O)
                  (if_then_else_M
                     (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4) (i 1)) &
                         (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                        (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 9)) O)
                     O)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M
                  ((EQ_M (to x3) (i 1)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                  (if_then_else_M
                     (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4))
                     acc O)
                  (if_then_else_M
                     (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4) (i 1)) &
                         (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                        (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 9)) O)
                     O))
               (if_then_else_M
                  (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4))
                  (if_then_else_M (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                     (if_then_else_M
                        ((EQ_M (to x4) (i 1)) &
                         (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                        (enc (pi1 (pi2 (dec x4 (sk (N 1))))) (m x1) (sr 9)) O)
                     O) O)) O)).
Definition t16 :=  (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
            (if_then_else_M (EQ_M (to x3) (i 2))
               (if_then_else_M
                  (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4))
                  (if_then_else_M
                     (EQ_M (reveal x5) (i 1)) & (EQ_M (m x1) (pk (N 2)))
                     (N 3)
                     (if_then_else_M
                        (EQ_M (reveal x5) (i 2)) & (EQ_M (m x1) (pk (N 2)))
                        (N 4) O)) O) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M
                  ((EQ_M (to x3) (i 1)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                  (if_then_else_M
                     (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4))
                     (if_then_else_M
                        (EQ_M (reveal x5) (i 1)) & (EQ_M (m x1) (pk (N 2)))
                        (N 3)
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 2)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 4) O)) O)
                  (if_then_else_M
                     (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4) (i 1)) &
                         (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 3)
                           (if_then_else_M
                              (EQ_M (reveal x5) (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 4) O)) O) O)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M
                  ((EQ_M (to x3) (i 1)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                  (if_then_else_M
                     (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4))
                     (if_then_else_M
                        (EQ_M (reveal x5) (i 1)) & (EQ_M (m x1) (pk (N 2)))
                        (N 3)
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 2)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 4) O)) O)
                  (if_then_else_M
                     (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4) (i 1)) &
                         (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 3)
                           (if_then_else_M
                              (EQ_M (reveal x5) (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 4) O)) O) O))
               (if_then_else_M
                  (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4))
                  (if_then_else_M (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                     (if_then_else_M
                        ((EQ_M (to x4) (i 1)) &
                         (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 3)
                           (if_then_else_M
                              (EQ_M (reveal x5) (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 4) O)) O) O) O)) O)).
Definition t26 :=  (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            ((EQ_M (to x2) (i 1)) & (EQ_M (pi1 (dec x2 (sk (N 1)))) (N 3))) &
            (EQ_M (pi2 (pi2 (dec x2 (sk (N 1))))) (m x1))
            (if_then_else_M (EQ_M (to x3) (i 2))
               (if_then_else_M
                  (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4))
                  (if_then_else_M
                     (EQ_M (reveal x5) (i 1)) & (EQ_M (m x1) (pk (N 2)))
                     (N 14)
                     (if_then_else_M
                        (EQ_M (reveal x5) (i 2)) & (EQ_M (m x1) (pk (N 2)))
                        (N 14)
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 3)
                           (if_then_else_M
                              (EQ_M (reveal x5) (i 1)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 4) O)))) O) O)
            (if_then_else_M (EQ_M (to x2) (i 2))
               (if_then_else_M
                  ((EQ_M (to x3) (i 1)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                  (if_then_else_M
                     (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4))
                     (if_then_else_M
                        (EQ_M (reveal x5) (i 1)) & (EQ_M (m x1) (pk (N 2)))
                        (N 14)
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 2)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5) (i 1)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 3)
                              (if_then_else_M
                                 (EQ_M (reveal x5) (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 4) O)))) O)
                  (if_then_else_M
                     (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4) (i 1)) &
                         (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5) (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 14)
                              (if_then_else_M
                                 (EQ_M (reveal x5) (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 3)
                                 (if_then_else_M
                                    (EQ_M (reveal x5) (i 1)) &
                                    (EQ_M (m x1) (pk (N 2))) 
                                    (N 4) O)))) O) O)) O))
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
               (if_then_else_M
                  ((EQ_M (to x3) (i 1)) &
                   (EQ_M (pi1 (dec x3 (sk (N 1)))) (N 3))) &
                  (EQ_M (pi2 (pi2 (dec x3 (sk (N 1))))) (m x1))
                  (if_then_else_M
                     (EQ_M (to x4) (i 2)) & (EQ_M (dec x4 (sk (N 2))) (N 4))
                     (if_then_else_M
                        (EQ_M (reveal x5) (i 1)) & (EQ_M (m x1) (pk (N 2)))
                        (N 14)
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 2)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5) (i 1)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 3)
                              (if_then_else_M
                                 (EQ_M (reveal x5) (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 4) O)))) O)
                  (if_then_else_M
                     (EQ_M (to x3) (i 2)) & (EQ_M (dec x3 (sk (N 2))) (N 4))
                     (if_then_else_M
                        ((EQ_M (to x4) (i 1)) &
                         (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5) (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 14)
                              (if_then_else_M
                                 (EQ_M (reveal x5) (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 3)
                                 (if_then_else_M
                                    (EQ_M (reveal x5) (i 1)) &
                                    (EQ_M (m x1) (pk (N 2))) 
                                    (N 4) O)))) O) O))
               (if_then_else_M
                  (EQ_M (to x2) (i 2)) & (EQ_M (dec x2 (sk (N 2))) (N 4))
                  (if_then_else_M (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                     (if_then_else_M
                        ((EQ_M (to x4) (i 1)) &
                         (EQ_M (pi1 (dec x4 (sk (N 1)))) (N 3))) &
                        (EQ_M (pi2 (pi2 (dec x4 (sk (N 1))))) (m x1))
                        (if_then_else_M
                           (EQ_M (reveal x5) (i 1)) &
                           (EQ_M (m x1) (pk (N 2))) 
                           (N 14)
                           (if_then_else_M
                              (EQ_M (reveal x5) (i 2)) &
                              (EQ_M (m x1) (pk (N 2))) 
                              (N 14)
                              (if_then_else_M
                                 (EQ_M (reveal x5) (i 1)) &
                                 (EQ_M (m x1) (pk (N 2))) 
                                 (N 3)
                                 (if_then_else_M
                                    (EQ_M (reveal x5) (i 1)) &
                                    (EQ_M (m x1) (pk (N 2))) 
                                    (N 4) O)))) O) O) O)) O)).
