        pose proof (@Vbuild_proper n CarrierA CarrierAe).
        unfold Proper, respectful in H.
        specialize
          (H (λ (z : nat) (zi : z < n),
            WriterMonadNoT.evalWriter
              (Rtheta2RStheta
               (mkValue
                (Vfold_right f
                (Vmap
                (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                (op Monoid_RthetaFlags
                (family_member Monoid_RthetaFlags op_family z zi)
                (rsvector2rvector i (Vmap Rtheta2RStheta x)))) uf_zero))))).
        specialize
          (H (λ (z : nat) (zi : z < n),
            (Vfold_right f
             (Vmap
             (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
             (op Monoid_RthetaFlags
             (family_member Monoid_RthetaFlags op_family z zi)
             (rsvector2rvector i (Vmap Rtheta2RStheta x)))) uf_zero))).
        specialize (H (fun _ _ => evalWriter_Rtheta2RStheta_mkValue_equiv)).
        rewrite H; clear H.
