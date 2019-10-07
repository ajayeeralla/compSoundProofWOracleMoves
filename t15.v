  (msg
      (if_then_else_M (EQ_M (reveal x1) (i 1)) O
         (if_then_else_M (EQ_M (reveal x1) (i 2)) O
            (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
               (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                  (if_then_else_M (EQ_M (reveal x2) (i 2)) O
                     (if_then_else_M (EQ_M (to x2) (i 1))
                        (if_then_else_M (EQ_M (reveal x3) (i 2)) O
                           (if_then_else_M
                              ((((EQ_M (reveal x3) (i 1)) &
                                 (EQ_M (to x2) (i 1))) & 
                                (EQ_M (to x1) (i 1))) &
                               (notb (EQ_M (act x2) new))) &
                              (EQ_M (act x1) new)
                              (if_then_else_M (EQ_M (reveal x4) (i 2)) O
                                 (if_then_else_M (EQ_M (to x4) (i 2)) grn4 O))
                              (if_then_else_M (EQ_M (to x3) (i 2))
                                 (if_then_else_M
                                    (EQ_M (reveal x4) (i 2)) &
                                    (EQ_M (to x1) (i 2)) mx1rn1
                                    (if_then_else_M
                                       (EQ_M (reveal x4) (i 2)) &
                                       (EQ_M (to x3) (i 2)) mx3rn3
                                       (if_then_else_M
                                          ((((EQ_M (reveal x4) (i 1)) &
                                             (EQ_M (to x2) (i 1))) &
                                            (EQ_M (to x1) (i 1))) &
                                           (notb (EQ_M (act x2) new))) &
                                          (EQ_M (act x1) new) mx2rn1 O))) O)))
                        (if_then_else_M (EQ_M (to x2) (i 2))
                           (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                              (if_then_else_M
                                 (EQ_M (reveal x3) (i 2)) &
                                 (EQ_M (to x1) (i 2))
                                 (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                                    (if_then_else_M 
                                       (EQ_M (to x4) (i 1)) acc O))
                                 (if_then_else_M
                                    (EQ_M (reveal x3) (i 2)) &
                                    (EQ_M (to x2) (i 2))
                                    (if_then_else_M 
                                       (EQ_M (reveal x4) (i 1)) O
                                       (if_then_else_M 
                                          (EQ_M (to x4) (i 1)) acc O))
                                    (if_then_else_M 
                                       (EQ_M (to x3) (i 1))
                                       (if_then_else_M
                                          (EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x1) (i 2)) mx1rn1
                                          (if_then_else_M
                                             (EQ_M (reveal x4) (i 2)) &
                                             (EQ_M (to x3) (i 2)) mx3rn3
                                             (if_then_else_M
                                                ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x2) (i 1))) &
                                                  (EQ_M (to x1) (i 1))) &
                                                 (notb (EQ_M (act x2) new))) &
                                                (EQ_M (act x1) new) mx2rn1 O)))
                                       O)))) O))))
               (if_then_else_M (EQ_M (to x1) (i 2))
                  (if_then_else_M (EQ_M (reveal x2) (i 1)) O
                     (if_then_else_M
                        (EQ_M (reveal x2) (i 2)) & (EQ_M (to x1) (i 2))
                        (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                           (if_then_else_M
                              (EQ_M (to x3) (i 1)) & (EQ_M (act x3) new)
                              (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                                 (if_then_else_M (EQ_M (to x4) (i 1)) acc O))
                              O))
                              
                              
                        (if_then_else_M
                           (EQ_M (to x2) (i 1)) & (EQ_M (act x2) new)
                           (if_then_else_M (EQ_M (reveal x3) (i 1)) O
                              (if_then_else_M
                                 (EQ_M (reveal x3) (i 2)) &
                                 (EQ_M (to x1) (i 2))
                                 (if_then_else_M (EQ_M (reveal x4) (i 1)) O
                                    (if_then_else_M 
                                       (EQ_M (to x4) (i 1)) acc O))
                                 (if_then_else_M
                                    (EQ_M (reveal x3) (i 2)) &
                                    (EQ_M (to x2) (i 2))
                                    (if_then_else_M 
                                       (EQ_M (reveal x4) (i 1)) O
                                       (if_then_else_M 
                                          (EQ_M (to x4) (i 1)) acc O))
                                    (if_then_else_M 
                                       (EQ_M (to x3) (i 1))
                                       (if_then_else_M
                                          (EQ_M (reveal x4) (i 2)) &
                                          (EQ_M (to x1) (i 2)) mx1rn1
                                          
                                          (if_then_else_M
                                             (EQ_M (reveal x4) (i 2)) &
                                             (EQ_M (to x3) (i 2)) mx3rn3
                                             (if_then_else_M
                                                ((((EQ_M (reveal x4) (i 1)) &
                                                  (EQ_M (to x2) (i 1))) &
                                                  (EQ_M (to x1) (i 1))) &
                                                 (notb (EQ_M (act x2) new))) &
                                                (EQ_M (act x1) new) mx2rn1 O)))
                                       O)))) O))) O)))))
