module type Branching =
 sig
   type s
    
   (** predicate (=s=) : s -> s -> bool *)
   (**  Assertion strict_s =  forall x:s, y:s,  x =s= y -> true
         
        Assertion extensional_s = 
          forall x:s, y:s,  true -> x =s= y -> x =s= y
         
        Assertion symmetric_s =  forall x:s, y:s,  x =s= y -> y =s= x
         
        Assertion transitive_s = 
          forall x:s, y:s, z:s,  x =s= y /\ y =s= z -> x =s= z
   *)
    
   (** branching types *)
    
   type t
    
   (** predicate (=t=) : s -> t -> t -> bool *)
   (**  Assertion strict_t =  forall x:s, y:t, z:t,  y =(t x)= z -> x : ||s||
         
        Assertion extensional_t = 
          forall x:s, y:s, z:t, w:t,  x =s= y -> z =(t x)= w -> z =(t y)= w
         
        Assertion symmetric_t = 
          forall x:s, y:t, z:t,  y =(t x)= z -> z =(t x)= y
         
        Assertion transitive_t = 
          forall x:s, y:t, z:t, w:t,  y =(t x)= z /\ z =(t x)= w ->
            y =(t x)= w
   *)
    
   (** branch labels *)
 end
 
module W : functor (B : Branching) ->
           sig
             type w
              
             (** predicate (=w=) : w -> w -> bool *)
             (**  Assertion strict_w =  forall x:w, y:w,  x =w= y -> true
                   
                  Assertion extensional_w = 
                    forall x:w, y:w,  true -> x =w= y -> x =w= y
                   
                  Assertion symmetric_w = 
                    forall x:w, y:w,  x =w= y -> y =w= x
                   
                  Assertion transitive_w = 
                    forall x:w, y:w, z:w,  x =w= y /\ y =w= z -> x =w= z
             *)
              
             val tree : B.s -> (B.t -> w) -> w
             (**  Assertion tree_support = 
                    let f = tree
                    in forall x:B.s, y:B.s,  x =B.s= y ->
                         (let x' = x
                          in (pfun phi : (B.t -> w) -> w =>
                               (pfun psi : (B.t -> w) -> w =>
                                 forall g:B.t -> w, h:B.t -> w, 
                                   (let r = g
                                    in (pfun f' : B.t -> w =>
                                         forall z:B.t, t:B.t, 
                                           (let y' = x' in =(B.t y')=) z t ->
                                           (let wild = z in =w=) (r z) 
                                           (f' t))) h ->
                                   (let wild = g in =w=) (phi g) (psi h)))) 
                         (f x) (f y)
             *)
              
             module Induction : functor (M : sig
                                               type ty_p
                                                
                                               (** predicate p : w -> ty_p -> bool *)
                                               (**  Assertion strict_p = 
                                                      forall x:w, a:ty_p, 
                                                        p x a -> x : ||w||
                                                     
                                                    Assertion extensional_p = 
                                                      forall x:w, y:w, 
                                                        a:ty_p,  x =w= y ->
                                                        p x a -> p y a
                                               *)
                                             end) ->
                                sig
                                  val induction : (B.s -> (B.t -> w) -> (B.t -> M.ty_p) -> M.ty_p) -> w -> M.ty_p
                                  (**  Assertion induction = 
                                         let phi = induction
                                         in forall f:B.s -> (B.t -> w) -> (B.t -> M.ty_p) -> M.ty_p, 
                                              (let g = f
                                               in forall x:B.s, 
                                                    x : ||B.s|| ->
                                                    let psi = g x
                                                    in forall f':B.t -> w, 
                                                         (let h = f'
                                                          in forall y:B.t, 
                                                               z:B.t, 
                                                               (let t = 
                                                                x
                                                                in =(B.t t)=) y z ->
                                                               (let wild = 
                                                                y in =w=) 
                                                               (h y) 
                                                               (h z)) ->
                                                         let xi = psi f'
                                                         in forall h:B.t -> M.ty_p, 
                                                              (let r = 
                                                               h
                                                               in forall y:B.t, 
                                                                    (
                                                                    let z = 
                                                                    x
                                                                    in ||B.t z||) y ->
                                                                    (
                                                                    let z = 
                                                                    f' y
                                                                    in 
                                                                    (pfun a : M.ty_p =>
                                                                    M.p z a)) 
                                                                    (
                                                                    r y)) ->
                                                              (let y = 
                                                               tree x f'
                                                               in (pfun a : M.ty_p =>
                                                                    M.p y a)) 
                                                              (xi h)) ->
                                              let g = phi f
                                              in forall t:w,  t : ||w|| ->
                                                   (let x = t
                                                    in (pfun a : M.ty_p =>
                                                         M.p x a)) (g t)
                                  *)
                                end
           end

