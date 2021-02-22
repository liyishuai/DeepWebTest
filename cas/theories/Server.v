From CAS Require Export
     App.

Variant randomE : Type -> Set :=
  Random__String : randomE string.

Fixpoint unwrap {R} (e : exp R) : R :=
  match e with
  | Exp__Const s    => s
  | Exp__Var   x    => ""
  | Exp__Match t tx => t =? unwrap tx
  end.

Class Is__cmE E `{appE id -< E} `{randomE -< E}.
Notation cmE := (appE id +' randomE).
Instance cmE_Is__cmE : Is__cmE cmE. Defined.

Definition concrete {E R} `{Is__cmE E} (m : itree smE R) : itree cmE R :=
  interp
    (fun _ e =>
       match e with
       | (ae|) =>
         match ae in appE _ Y return _ Y with
         | App__Send c r =>
           match r with
           | Response__NotModified => embed App__Send c Response__NotModified
           | Response__NoContent   => embed App__Send c Response__NoContent
           | Response__PreconditionFailed =>
             embed App__Send c Response__PreconditionFailed
           | Response__OK tx vx =>
             embed App__Send c $ Response__OK (unwrap tx : id tag)
                                          (unwrap vx : id value)
           end
         | App__Recv ss => embed App__Recv []
         end
       | (|se) =>
         match se in symE _ Y return _ Y with
         | Sym__Fresh     => str <- trigger Random__String;; ret (Exp__Const str)
         | Sym__Decide bx => ret (unwrap bx)
         end
       end) m.
