load_mode[0] = 1;
/** {33;done} **/

declare_package(`functions);
/** {34;done} **/

clear_event(start_functions);
/** the event start_functions is not present **/

define start_functions true;
/** event 1 max 0 net 0 **/

where();
/** {after 1 start_functions;} **/

clear_event(preimage);
/** after 1 start_functions; **/

define preimage(sigma:type, tau:type, y:tau, f:sigma=>tau){
  assert(x:sigma){f(x)=y}};
/** event 2 max 354 net 354 **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** event 3 max 922 net 275 **/

theorem test_injectivity (tau:type,sigma:type,
                          f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){ 
  x_2=x_3}{
  classify(f(x_3)) //realize that f(x_3) has a unique preimage under f
  };
/** event 4 max 1825 net 221 **/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** event 5 max 1957 net 177 **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/** event 6 max 2348 net 122 **/

theorem bijections_invert(tau:type,sigma:type,inhabited(bijection(tau,sigma))){
  inhabited(bijection(sigma,tau))
  }{
  using(
        f:bijection(tau,sigma),
        g = lambda(x:sigma){the(y:tau){f(y)=x}}
        //intern_cps(lambd(x:sigma){...})
        ///decl(x:sigma)
        ////intern_cps(the(assert(y:tau){f(y)=x}))
        
        /////backchain(inhabited(assert(...)))
        //////analyze(inhabited(...))
        ///////classify(f) binds a surjection variable to f
        ///////yields forall(y:tau)exists(x:sigma)f(x)=y
        ///////yields exists(x:sigma)f(x)=y
        ///////yields the backchain goal.
        
        /////backchain(unique(assert(...)))
        //////analyze(unique(...))
        ///////classify(f) binds an injection variable to f.
        ///////yields forall(y:sigma){unique(assert(x:tau){f(x) = y})}
        ///////yields unique(x:sigma)f(x)=y
        ///////yields the backchain goal.
        
        
        //analyze(g)
        ///classify(f) generates the desired habitation and uniquenes formulas
        //    A.forall(x:sigma){inhabited(preimage(x,f))}
        //    B.forall(x:sigma){unique(preimage(x,f))}
        //    C.f:tau=>sigma
        //classify(g) then places g under bijection which proves the goal.
        //    1.show(forall(x:tau){inhabited(preimage(x,[g@mvar:sigma=>tau]))}
        //    2.show(forall(x:tau){unique(preimage(x,[g@mvar:sigma=>tau]))}
        //    3.show(inhabited(preimage(gvar(tau),[g@mvar:sigma=>tau]))
        //    4.show(unique(preimage(gvar(tau),[g@mvar:sigma=>tau]))
        //    5.show(inhabited(assert(y:sigma){[g@mvar:sigma=>tau](y)=gvar(tau)}))  //step1: create gvar(sigma)
        //    6.show(unique(assert(y:sigma){[g@mvar:sigma=>tau](y)=gvar(tau)}))
        //    7.show(inhabited(assert(y:sigma){the(z:tau){f(z)=y}=gvar(tau)}))
        //    8.show(unique(assert(y:sigma){the(z:tau){f(z)=y}=gvar(tau)}))

        //    9.the(z:tau){f(z)=f(gvar(tau))} = gvar(tau)    //using existential witness f(gvar(tau))

        //the(z:tau){f(z)=y}=gvar(tau)  iff  y=f(gvar(tau)) && gvar(tau):tau

        //11.the(z:rho){phi[y,z]}=c iff (phi[y,c] && c:rho)    //step2: alternative matrix for goal

        //(renamed x to y)

        //13.show(exists(y:sigma){y=f(gvar(tau))})  //step3: notice this silly kind of existential goal somehow
        //14.show(unique(assert(y:sigma){y=f(gvar(tau))}))
        //15.show(is(f(gvar(tau)),sigma))  //done  eg from f(gvar(tau)) = f(gvar(tau))
        ){	
    witness(g)
    }};
/** event 6 max 2285 net 304 **/



