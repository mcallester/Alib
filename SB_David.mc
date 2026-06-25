
restart_event(`schroeder_bernstein_functions);
/** {35;done} **/

declare_package(`schroeder_bernstein_functions);
/** {36;done} **/

/** ========================================================================
empty set exists
========================================================================**/

package[0]
/** {
    37;
    schroeder_bernstein_functions} **/

check_for_corruption[0] = 1;
/** {38;done} **/

proof_stepping[0] = 0;
/** {39;done} **/

intern_stepping[0] = 0;
/** {40;done} **/

current_events[0]
/** {41;} **/

break_on_user_error[0] = 0;
/** {42;done} **/

// ========= voodoo block
clear_event(sets_exist);
/** sets_exist has not been defined as an event **/

//intern_hook[0]=NULL;

// compile new code here

theorem sets_exist (foo:type){inhabited(set_of(foo))}{sorry};
/** {43;done} **/

finish_event();
/** there is no suspended event to finish **/

// ====== end of voodoo block ====

clear_event(test1);
/** test1 has not been defined as an event **/

theorem test1(tau:type){forall(x:assert(xx:tau){not(equal(xx,xx))}){false}};
/** {
    in event test1;
    1.show_decl(tau:type);
    2.intern_decl(x:assert(bound_x:tau){
                    not(equal(bound_x,bound_x))});
    unexpected contradiction} **/

finish_event();
/** there is no suspended event to finish **/


clear_event(test2)
/** test2 has not been defined as an event **/

theorem test2(tau:type){forall(x:assert(xx:tau){not(equal(xx,xx))}){not(is(x,tau))}}{
  suppose_not;
};
/** {
    in event test2;
    1.show_decl(tau:type);
    2.intern_decl(x:assert(bound_x:tau){
                    not(equal(bound_x,bound_x))});
    unexpected contradiction} **/

clear_event(emptyset_exists);
/** emptyset_exists has not been defined as an event **/

proof_stepping[0]=1;
/** {44;done} **/

theorem emptyset_exists(tau:type){exists(s:set_of(tau)){empty(in(s))}
  }{
  //show{empty(in(the_set(x:tau){not(x=x)}))};
  classify(the_set(x:tau){not(x=x)})
  };
/** {
    in event emptyset_exists;
    1.show_decl(tau:type);
    2.push_goal(exists(bound_x:set_of(tau)){empty(in(bound_x))});
    3.classifying the_set(x:tau){not(x=x)};
    4.analyzing the_set(x:tau){not(x=x)};
    goal achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

finish_event();
/** {44;done} **/

int x[0]=1;
/** {45;done} **/

/** ========================================================================
preimage
========================================================================**/
/** ========================================================================
//do the next two the first time

//int intern_hook_count[0]=0;

//set_intern_hook(mze){if(mze->constructor==conservative){intern_hook_count[0]++;}};
//set_intern_hook(mze){intern_hook_count[0]++;};

//do the next two the second time (after clearing preimage).

//int num_desired[0]=10;

//set_intern_hook(mze){
  //  if(intern_hook_count[0] && (random()%intern_hook_count[0])<num_desired[0]){
    //    mcpprint(sugar(mze));}
  //  };
========================================================================**/

exp_limit[0]=500000;
/** {46;done} **/

clear_event(preimage);
/** preimage has not been defined as an event **/

define preimage(tau:type, sigma:type, y:sigma, h:tau=>sigma){
  assert(x:tau){h(x)=y}};
/** {47;done} **/

finish_event();
/** there is no suspended event to finish **/

int_exp(max_total[0])
/** {48;2211} **/

clear_event(injection);
/** injection has not been defined as an event **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** {49;done} **/

finish_event();
/** there is no suspended event to finish **/

//int_exp(intern_hook_count[0])

//event_max_counts()
int_exp(max_total[0])
/** {50;1856} **/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** {51;done} **/

finish_event();
/** there is no suspended event to finish **/

int_exp(max_total[0])
/** {52;3082} **/

clear_event(bijection)
/** bijection has not been defined as an event **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/** {53;done} **/

finish_event();
/** there is no suspended event to finish **/

int_exp(max_total[0])
/** {54;4017} **/

clear_event(bijections_invert);
/** bijections_invert has not been defined as an event **/

proof_stepping[0]=1;
/** {55;done} **/

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
/** {
    in event bijections_invert;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_assume(inhabited(bijection(tau,sigma)));
    4.push_goal(inhabited(bijection(sigma,tau)));
    5.using_decl(f:bijection(tau,sigma));
    6.intern_decl(x:sigma);
    7.push_goal(exists(bound_x:tau){equal(f(bound_x),x)});
    8.backchaining(exists(bound_x:tau){equal(f(bound_x),x)});
    9.analyzing x;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

finish_event();
/** {
    in event bijections_invert;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_assume(inhabited(bijection(tau,sigma)));
    4.push_goal(inhabited(bijection(sigma,tau)));
    5.using_decl(f:bijection(tau,sigma));
    6.define(g,
             lambda(bound_x:sigma){
               the(assert(bound_x_2:tau){
                     equal(f(bound_x_2),bound_x)})});
    goal failed,looping step of classifying g;
    7.classifying g;
    8.analyzing f;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/


step();
/** {
    in event bijections_invert;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_assume(inhabited(bijection(tau,sigma)));
    4.push_goal(inhabited(bijection(sigma,tau)));
    5.using_decl(f:bijection(tau,sigma));
    6.define(g,
             lambda(bound_x:sigma){
               the(assert(bound_x_2:tau){
                     equal(f(bound_x_2),bound_x)})});
    goal failed,looping step of classifying g;
    7.classifying g;
    completed analyzing f;
    8.analyzing g;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/


class_of(unique(preimage([gvar:tau#0], [mvar:arrow(sigma,tau)#0])))
/** {
    56;
    1:unique(preimage(sigma,
                      tau,
                      [gvar:tau#0],
                      [g@arrow(sigma,tau)#0]));} **/

int_exp(showp(item(1)))
/** {57;1} **/

mzexp mv[0] = intern_exp(`{[mvar:preimage(sigma, tau, [gvar:tau#0], [g@arrow(sigma,tau)#0])#0]});
/** {59;done} **/

mv[0]=mvar_gensym(intern_exp(`{preimage(sigma, tau, [gvar:tau#0], [g@arrow(sigma,tau)#0])}),NULL);
/** {62;done} **/



sugar(mv[0])
/** {
    63;
    [mvar:lambda(bound_fun:arrow(sigma,tau)){
       assert(bound_x:sigma){
         equal(bound_fun(bound_x),
               [gvar:tau#0])}}([g@arrow(sigma,tau)#0])#0]} **/

sugar(mv[0]->arg1)
/** {
    64;
    assert(bound_x:sigma){
      equal([g@arrow(sigma,tau)#0](bound_x),
            [gvar:tau#0])}} **/

sugar(unnormalize(mv[0]->arg1))
/** {
    65;
    lambda(bound_fun:arrow(sigma,tau)){
      assert(bound_x:sigma){
        equal(bound_fun(bound_x),
              [gvar:tau#0])}}([g@arrow(sigma,tau)#0])} **/


int_exp(beta_reducesp())

class_of(assert(bound_x:sigma){
      equal([g@arrow(sigma,tau)#0](bound_x),
            [gvar:tau#0])})
/** {
    66;
    1:assert(bound_x:sigma){
      equal([g@arrow(sigma,tau)#0](bound_x),
            [gvar:tau#0])};
    2:assert(bound_x:sigma){
      equal([g@assert(bound_fun:arrow(sigma,tau)){
               forall(bound_x:tau){
                 inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#1](bound_x),
            [gvar:tau#0])};
    3:preimage(sigma,
               tau,
               [gvar:tau#0],
               [g@assert(bound_fun:arrow(sigma,tau)){
                  forall(bound_x:tau){
                    inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#1]);
    4:assert(bound_x:sigma){
      equal([g@assert(bound_fun:arrow(sigma,tau)){
               forall(bound_x:tau){
                 inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#0](bound_x),
            [gvar:tau#0])};
    5:preimage(sigma,
               tau,
               [gvar:tau#0],
               [g@assert(bound_fun:arrow(sigma,tau)){
                  forall(bound_x:tau){
                    inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#0]);
    6:preimage(sigma,
               tau,
               [gvar:tau#0],
               [g@arrow(sigma,tau)#0]);
    7:lambda(bound_fun:arrow(sigma,tau)){
      assert(bound_x:sigma){
        equal(bound_fun(bound_x),
              [gvar:tau#0])}}([g@arrow(sigma,tau)#0]);} **/

mzexp reduct[0] = beta_reduction(item(6)->arg1,item(6)->arg2);
/** {67;done} **/

sugar(reduct[0])
/** {68;[gvar:tau#0]} **/

sugar(item(6)->arg1)
/** {
    69;
    preimage(sigma,tau,[gvar:tau#0])} **/

sugar(item(6)->arg2)
/** {70;[g@arrow(sigma,tau)#0]} **/

int_exp(mv[0]->arg1 == normal_form(mv[0]->arg1))
/** {61;0} **/


class_of(preimage(sigma, tau, [gvar:tau#0], [g@arrow(sigma,tau)#0]))
/** {
    58;
    1:assert(bound_x:sigma){
      equal([g@arrow(sigma,tau)#0](bound_x),
            [gvar:tau#0])};
    2:assert(bound_x:sigma){
      equal([g@assert(bound_fun:arrow(sigma,tau)){
               forall(bound_x:tau){
                 inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#1](bound_x),
            [gvar:tau#0])};
    3:preimage(sigma,
               tau,
               [gvar:tau#0],
               [g@assert(bound_fun:arrow(sigma,tau)){
                  forall(bound_x:tau){
                    inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#1]);
    4:assert(bound_x:sigma){
      equal([g@assert(bound_fun:arrow(sigma,tau)){
               forall(bound_x:tau){
                 inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#0](bound_x),
            [gvar:tau#0])};
    5:preimage(sigma,
               tau,
               [gvar:tau#0],
               [g@assert(bound_fun:arrow(sigma,tau)){
                  forall(bound_x:tau){
                    inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#0]);
    6:preimage(sigma,
               tau,
               [gvar:tau#0],
               [g@arrow(sigma,tau)#0]);
    7:lambda(bound_fun:arrow(sigma,tau)){
      assert(bound_x:sigma){
        equal(bound_fun(bound_x),
              [gvar:tau#0])}}([g@arrow(sigma,tau)#0]);} **/

int_exp(showp(intern_exp(`{inhabited(preimage([gvar:tau#0],g))})))
/** {60;0} **/

class_of(inhabited(preimage([gvar:tau#0],g)))
/** {
    61;
    1:is(f(gvar(tau,kurt_zero)),
         sigma);
    2:inhabited(preimage(sigma,
                         tau,
                         gvar(tau,kurt_zero),
                         g));
    3:exists(bound_x:sigma){
      equal(g(bound_x),
            gvar(tau,kurt_zero))};
    4:exists(bound_x:sigma){
      equal([g@assert(bound_fun:arrow(sigma,tau)){
               forall(bound_x:tau){
                 inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#0](bound_x),
            gvar(tau,kurt_zero))};
    5:inhabited(preimage(sigma,
                         tau,
                         gvar(tau,kurt_zero),
                         [g@assert(bound_fun:arrow(sigma,tau)){
                            forall(bound_x:tau){
                              inhabited(preimage(sigma,tau,bound_x,bound_fun))}}#0]));
    6:exists(bound_x:sigma){
      equal([g@arrow(sigma,tau)#0](bound_x),
            gvar(tau,kurt_zero))};
    7:inhabited(preimage(sigma,
                         tau,
                         gvar(tau,kurt_zero),
                         [g@arrow(sigma,tau)#0]));} **/

int_exp(item(7)->show)
/** {62;1} **/

int_exp(truep(item(7)))
/** {64;1} **/

int_exp(item(2)->show)
/** {63;0} **/

why_true(is(g,injection(sigma,tau)))
/** {66;unknown} **/

class_of(preimage(sigma,
                         tau,
                         gvar(tau,kurt_zero),
                         [g@arrow(sigma,tau)#0]))
/**  **/

exists(x:sigma){matrix[x]}  --->  matrix([gvar:sigma]) == matrix2([gvar:sigma]) -?-> exists(x:sigma){matrix2[x]}

    matrix([gvar:sigma]) == x=c   --> equate original existential to c:sigma


/** {
    in event bijections_invert;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_assume(inhabited(bijection(tau,sigma)));
    4.push_goal(inhabited(bijection(sigma,tau)));
    5.using_decl(f:bijection(tau,sigma));
    6.intern_decl(x:sigma);
    7.push_goal(inhabited(assert(bound_x:tau){equal(f(bound_x),x)}));
    8.backchaining(inhabited(assert(bound_x:tau){equal(f(bound_x),x)}));
    9.analyzing x;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/


finish_goal();
/** {
    in event bijections_invert;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_assume(inhabited(bijection(tau,sigma)));
    4.push_goal(inhabited(bijection(sigma,tau)));
    5.using_decl(f:bijection(tau,sigma));
    6.intern_decl(x:sigma);
    proved(inhabited(assert(bound_x:tau){equal(f(bound_x),x)}));
    7.push_goal(unique(assert(bound_x:tau){equal(f(bound_x),x)}));
    8.backchaining(unique(assert(bound_x:tau){equal(f(bound_x),x)}));
    9.analyzing x;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

finish_goal();
/** {
    in event bijections_invert;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_assume(inhabited(bijection(tau,sigma)));
    4.push_goal(inhabited(bijection(sigma,tau)));
    5.using_decl(f:bijection(tau,sigma));
    6.define(g,
             lambda(bound_x:sigma){
               the(assert(bound_x_2:tau){
                     equal(f(bound_x_2),bound_x)})});
    7.classifying g;
    8.analyzing f;
    goal not achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

types_of(f)
/** {
    62;
    1:bijection(tau,sigma);
    2:lambda(bound_s:type){
      assert(bound_fun:arrow(tau,bound_s)){
        and(is(bound_fun,
               injection(tau,bound_s)),
            is(bound_fun,
               surjection(tau,bound_s)))}}(sigma);
    3:lambda(bound_s:type){
      assert(bound_fun:arrow(tau,bound_s)){
        forall(bound_x:bound_s){
          unique(preimage(tau,
                          bound_s,
                          bound_x,
                          bound_fun))}}}(sigma);
    4:lambda(bound_s:type){
      assert(bound_fun:arrow(tau,bound_s)){
        forall(bound_x:bound_s){
          inhabited(preimage(tau,
                             bound_s,
                             bound_x,
                             bound_fun))}}}(sigma);
    5:arrow(tau,sigma);
    6:surjection(tau,sigma);
    7:injection(tau,sigma);
    8:assert(bound_fun:arrow(tau,sigma)){
      forall(bound_x:sigma){
        inhabited(preimage(tau,sigma,bound_x,bound_fun))}};
    9:assert(bound_fun:arrow(tau,sigma)){
      forall(bound_x:sigma){
        unique(preimage(tau,sigma,bound_x,bound_fun))}};
    10:assert(bound_fun:arrow(tau,sigma)){
      and(is(bound_fun,
             injection(tau,sigma)),
          is(bound_fun,
             surjection(tau,sigma)))};} **/


step();
/** {
    in event bijections_invert;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_assume(inhabited(bijection(tau,sigma)));
    4.push_goal(inhabited(bijection(sigma,tau)));
    5.using_decl(f:bijection(tau,sigma));
    6.intern_decl(x:sigma);
    7.push_goal(inhabited(assert(bound_x:tau){equal(f(bound_x),x)}));
    8.backchaining(inhabited(assert(bound_x:tau){equal(f(bound_x),x)}));
    completed analyzing x;
    9.analyzing f;
    goal achieved;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

finish_event();
/** {
    in event bijections_invert;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_assume(inhabited(bijection(tau,sigma)));
    4.push_goal(inhabited(bijection(sigma,tau)));
    proved(forall(bound_fun:bijection(tau,sigma)){
             implies(is(lambda(bound_x:sigma){
                          the(assert(bound_x_2:tau){
                                equal(bound_fun(bound_x_2),
                                      bound_x)})},
                        injection(sigma,tau)),
                     implies(is(lambda(bound_x:sigma){
                                  the(assert(bound_x_2:tau){
                                        equal(bound_fun(bound_x_2),
                                              bound_x)})},
                                surjection(sigma,tau)),
                             inhabited(bijection(sigma,tau))))});
    5.backchaining(inhabited(bijection(sigma,tau)));
    Failure to show inhabited(bijection(sigma,tau))} **/


finish_event();
/** there is no suspended event to finish **/

int_exp(max_total[0])
/** {79;4979} **/

clear_event(empty_uniqueness);
/** empty_uniqueness has not been defined as an event **/

theorem empty_uniqueness (tau:type) {
  unique(assert(s:set_of(tau)){empty(in(s))})}{
  show(x1:assert(s:set_of(tau)){empty(in(s))},
       x2:assert(s:set_of(tau)){empty(in(s))}){
    x1=x2}};
/** {80;done} **/

finish_event();
/** there is no suspended event to finish **/

clear_event(test_injectivity);
/** test_injectivity has not been defined as an event **/

proof_stepping[0]=1;
/** {87;done} **/

//preimage(f,f(x_2)) =   assert(x:tau){f(x)=f(x_2)}

theorem test_injectivity (tau:type,sigma:type,
                          f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){ //x_3:preimage(f,f(x_2))
  x_2=x_3}{
  classify(f)
  };
/** {
    in event test_injectivity;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_decl(f:injection(tau,sigma));
    4.show_decl(x_2:tau);
    5.show_decl(x_3:tau);
    6.show_assume(equal(f(x_2),f(x_3)));
    7.push_goal(equal(x_2,x_3));
    completed classifying f;
    8.backchaining(equal(x_2,x_3));
    completed analyzing x_2;
    completed analyzing x_3;
    Failure to show equal(x_2,x_3)} **/

step();
/** {
    in event test_injectivity;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_decl(f:injection(tau,sigma));
    4.show_decl(x_2:tau);
    5.show_decl(x_3:tau);
    6.show_assume(equal(f(x_2),f(x_3)));
    completed analyzing tau;
    7.analyzing sigma;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

int_exp(intern_exp(`{arrow(tau,sigma)})->upsilon)
/** {88;0} **/

step();
/** {
    in event test_injectivity;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_decl(f:injection(tau,sigma));
    4.show_decl(x_2:tau);
    5.show_decl(x_3:tau);
    6.show_assume(equal(f(x_2),f(x_3)));
    completed analyzing tau;
    completed analyzing sigma;
    7.analyzing f;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/


sugar_context(ucontext[0])
/** {
    86;
    in event test_injectivity;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_decl(f:injection(tau,sigma));
    4.show_decl(x_2:tau);
    5.show_decl(x_3:tau);
    6.show_assume(equal(f(x_2),f(x_3)));
    completed analyzing tau;
    completed analyzing sigma;
    7.analyzing f;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

int_exp(mz_find(intern_exp(`tau))->upsilon)
/** {89;1} **/

types_of(f)
/** {
    87;
    1:arrow([tau@type#0],[sigma@type#1]);
    2:surjection([tau@type#0],[sigma@type#1]);
    3:assert(bound_fun:arrow([tau@type#0],[sigma@type#1])){
      forall(bound_x:[sigma@type#1]){
        unique(preimage([tau@type#0],
                        [sigma@type#1],
                        bound_x,
                        bound_fun))}};
    4:injection(tau,sigma);
    5:assert(bound_fun:arrow(tau,[sigma@type#1])){
      forall(bound_x:[sigma@type#1]){
        unique(preimage(tau,
                        [sigma@type#1],
                        bound_x,
                        bound_fun))}};
    6:lambda(bound_s:type){
      assert(bound_fun:arrow(tau,bound_s)){
        forall(bound_x:bound_s){
          unique(preimage(tau,
                          bound_s,
                          bound_x,
                          bound_fun))}}}([sigma@type#1]);
    7:lambda(bound_s:type){
      assert(bound_fun:arrow([tau@type#0],bound_s)){
        forall(bound_x:bound_s){
          unique(preimage([tau@type#0],
                          bound_s,
                          bound_x,
                          bound_fun))}}}([sigma@type#1]);
    8:assert(bound_fun:arrow(tau,sigma)){
      forall(bound_x:sigma){
        unique(preimage(tau,sigma,bound_x,bound_fun))}};
    9:arrow(tau,sigma);
    10:arrow(tau,[sigma@type#1]);
    11:assert(bound_fun:arrow([tau@type#0],[sigma@type#1])){
      forall(bound_x:[sigma@type#1]){
        inhabited(preimage([tau@type#0],
                           [sigma@type#1],
                           bound_x,
                           bound_fun))}};
    12:lambda(bound_s:type){
      assert(bound_fun:arrow([tau@type#0],bound_s)){
        forall(bound_x:bound_s){
          inhabited(preimage([tau@type#0],
                             bound_s,
                             bound_x,
                             bound_fun))}}}([sigma@type#1]);
    13:assert(bound_fun:arrow([tau@type#0],[sigma@type#1])){
      and(is(bound_fun,
             injection([tau@type#0],[sigma@type#1])),
          is(bound_fun,
             surjection([tau@type#0],[sigma@type#1])))};
    14:bijection([tau@type#0],[sigma@type#1]);
    15:lambda(bound_s:type){
      assert(bound_fun:arrow([tau@type#0],bound_s)){
        and(is(bound_fun,
               injection([tau@type#0],bound_s)),
            is(bound_fun,
               surjection([tau@type#0],bound_s)))}}([sigma@type#1]);
    16:injection([tau@type#0],[sigma@type#1]);} **/

step();
/** {
    in event test_injectivity;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_decl(f:injection(tau,sigma));
    4.show_decl(x_2:tau);
    5.show_decl(x_3:tau);
    6.show_assume(equal(f(x_2),f(x_3)));
    completed analyzing tau;
    7.analyzing sigma;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

step();
/** {
    in event test_injectivity;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_decl(f:injection(tau,sigma));
    4.show_decl(x_2:tau);
    5.show_decl(x_3:tau);
    6.show_assume(equal(f(x_2),f(x_3)));
    completed analyzing tau;
    completed analyzing sigma;
    7.analyzing f;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/

why_true(unique(preimage(f(x_2),f)))
/** {59;unknown} **/

why_true(is(f,assert(ff:arrow(tau,sigma)){forall(xx:sigma){unique(preimage(xx,ff))}}))
/** {
    60;
    {
      truth_of(is(f,
                  assert(bound_fun:arrow(tau,sigma)){
                    forall(bound_x:sigma){
                      unique(preimage(tau,sigma,bound_x,bound_fun))}}));
      follows by truth_transfer from;
      1:truth_of(is([f@injection([tau@type#0],[sigma@type#1])#0],
                    injection([tau@type#0],[sigma@type#1])));
      2:same_find(is(f,
                     assert(bound_fun:arrow(tau,sigma)){
                       forall(bound_x:sigma){
                         unique(preimage(tau,sigma,bound_x,bound_fun))}}),
                  is([f@injection([tau@type#0],[sigma@type#1])#0],
                     injection([tau@type#0],[sigma@type#1])))}} **/


why_true(forall(xx:sigma){unique(preimage(xx,f))})
/** {
    61;
    {
      truth_of(forall(bound_x:sigma){
                 unique(preimage(tau,sigma,bound_x,f))});
      follows by truth_transfer from;
      1:truth_of(forall(bound_x:[sigma@type#1]){
                   unique(preimage([tau@type#0],
                                   [sigma@type#1],
                                   bound_x,
                                   [f@assert(bound_fun:arrow([tau@type#0],[sigma@type#1])){
                                      forall(bound_x:[sigma@type#1]){
                                        unique(preimage([tau@type#0],
                                                        [sigma@type#1],
                                                        bound_x,
                                                        bound_fun))}}#0]))});
      2:same_find(forall(bound_x:sigma){
                    unique(preimage(tau,sigma,bound_x,f))},
                  forall(bound_x:[sigma@type#1]){
                    unique(preimage([tau@type#0],
                                    [sigma@type#1],
                                    bound_x,
                                    [f@assert(bound_fun:arrow([tau@type#0],[sigma@type#1])){
                                       forall(bound_x:[sigma@type#1]){
                                         unique(preimage([tau@type#0],
                                                         [sigma@type#1],
                                                         bound_x,
                                                         bound_fun))}}#0]))})}} **/

why_true(is(f(x_2),sigma))
/** {
    62;
    {
      truth_of(is(f(x_2),sigma));
      follows by self_type from;
      1:safety_of(f(x_2))}} **/

class_of(f(x_2))
/** {
    65;
    1:f(x_3);
    2:[f@injection([tau@type#0],[sigma@type#1])#0]([x_3@[tau@type#0]#1]);
    3:[f@injection([tau@type#0],[sigma@type#1])#0]([x_2@[tau@type#0]#0]);
    4:[f@assert(bound_fun:arrow([tau@type#0],[sigma@type#1])){
         forall(bound_x:[sigma@type#1]){
           unique(preimage([tau@type#0],
                           [sigma@type#1],
                           bound_x,
                           bound_fun))}}#0]([x_2@[tau@type#0]#0]);
    5:[f@assert(bound_fun:arrow([tau@type#0],[sigma@type#1])){
         forall(bound_x:[sigma@type#1]){
           unique(preimage([tau@type#0],
                           [sigma@type#1],
                           bound_x,
                           bound_fun))}}#0]([x_3@[tau@type#0]#1]);
    6:[f@assert(bound_fun:arrow([tau@type#0],[sigma@type#1])){
         forall(bound_x:[sigma@type#1]){
           inhabited(preimage([tau@type#0],
                              [sigma@type#1],
                              bound_x,
                              bound_fun))}}#0]([x_2@[tau@type#0]#0]);
    7:[f@assert(bound_fun:arrow([tau@type#0],[sigma@type#1])){
         forall(bound_x:[sigma@type#1]){
           inhabited(preimage([tau@type#0],
                              [sigma@type#1],
                              bound_x,
                              bound_fun))}}#0]([x_3@[tau@type#0]#1]);
    8:[f@arrow([tau@type#0],[sigma@type#1])#0]([x_2@[tau@type#0]#0]);
    9:[f@arrow([tau@type#0],[sigma@type#1])#0]([x_3@[tau@type#0]#1]);
    10:f(x_2);} **/

step();
/** {
    in event test_injectivity;
    1.show_decl(tau:type);
    2.show_decl(sigma:type);
    3.show_decl(f:injection(tau,sigma));
    4.show_decl(x_2:tau);
    5.show_decl(x_3:tau);
    6.show_assume(equal(f(x_2),f(x_3)));
    completed analyzing tau;
    completed analyzing sigma;
    completed analyzing f;
    7.analyzing x_2;
    to continue run step(),finish_goal(),finish_event()or abort_event();} **/


types_of(f)
/** {
    60;
    1:injection(tau,sigma);
    2:injection([tau@type#0],[sigma@type#1]);} **/




finish_event();

clear_event(Schroeder_Bernstein);

theorem Schroeder_Bernstein (
			     tau:type,
			     sigma:type,
			     inhabited(injection(sigma,tau)),
			     inhabited(injection(tau,sigma))){
  inhabited(bijection(tau,sigma))
  }{
  
  using(
	f:injection(sigma,tau),
	g:injection(tau,sigma),
	usef =mu assert(x:sigma){not(exists(y:tau){not(is(g(y),usef)) && g(y) = x})},
	h = lambda(x:sigma){if(is(x,usef),f(x),the(y:tau){g(y)=x})}
	//cps_intern of h
	//decl(x:sigm)
	//suppose(not(is(x,usef)))
	///yields not(not(exists(y:tau){not(is(g(y),usef))}))
	///yields (exists(y:tau){not(is(g(y),usef))})
	///yields exists(y:tau){not(not(g(y) = x))} unrolling usef in the above and reducing to one of the conjuncts.
	///yields exists(y:tau){g(y) = x}
	///yields that h is safe.
	){
    
    show(is(h,surjection)){
      using(let_be(y:tau)){
	show(exists(x:sigma){h(x) = y}){
	  using(is(g(y),usef)){witness(the(x:sigma){f(x) = y})}
	  using(not(is(g(y),usef))){witness(g(y))}}}}
	
    show(is(h,injection)){
      using(let_be(x1,x2:sigma)){
        suppose(h(x1) = h(x2)){
          show(x1=x2){
            using(assume(is(g(f(x1)),usef))),
              using(assume(not(is(g(f(x1)),usef))))}}}}}};

why_true(not(not(exists(y:tau){not(is(g(y),usef))})))
/**  **/

types_of(g(y))

types_of(usef)


//WORKING PROOF OF INJECTION SUPERSEDED ABOVE
// injection works but needs exploration. Also still want to try the() and taxonomic
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  with(f:injection(s,w),
       g:injection(w,s),
       use_f =μ lambda(x:s){
         not(exists(y:preimage(w,s,x,g)){
               not(exists(z:preimage(s,w,y,f)){
                     use_f(z)})})}){
    with(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
      show(){is(h,injection(s,w))}{
        show(x:s){use_f(x) |=> f(x)=h(x)};
        show(x:s){not(use_f(x)) |=> the(y:w){g(y)=x}=h(x)};
        show(y:w){unique(preimage(s,w,y,f))};
        show(x:s){unique(preimage(w,s,x,g))};
        
        //show(x:s){is(preimage(w,s,x,g),w)}; need guidance on this
        
        show(x:s, //apply fixed point of use_f
             not(use_f(x)),
             y:preimage(w,s,x,g),
             xx:preimage(s,w,y,f)){
          not(use_f(xx))}{
          with(yy:assert(yyy:preimage(w,s,x,g)){
                 not(exists(xxx:preimage(s,w,yyy,f)){use_f(xxx)})}){
            show{yy=y}{with(focus(y), focus(yy))};}};
        
        //explore why this doesn't eliminate the body in show_case_contradictory
        //show(x:s,
               //   not(use_f(x))){
          //forall(y:preimage(w,s,x,g)){
            //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
        show(x_1:w,
             x_2:preimage(s,w,x_1,h),
             x_3:preimage(s,w,x_1,h)){
          x_2 = x_3
          }{
          show_case_contradictory(use_f(x_2) && not(use_f(x_3))){
            with(focus(x_3), focus(x_1), focus(x_2)){
              //show{forall(y:preimage(w,s,x_3,g)){
                  //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              show{forall(y:preimage(w,s,x_3,g)){
                  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              }};
          show_case_contradictory(use_f(x_3) && not(use_f(x_2))){
            with(focus(x_3), focus(x_1), focus(x_2))};
          with(assume_not_goal,focus(x_2), focus(x_3)){
            show_case(use_f(x_3))}}};
      show(){is(h,surjection(s,w))}{
        show(x1:w){exists(x2:s){h(x2)=x1}}{
          show_case(use_f(g(x1))){
            with(focus(g(x1)),
                 z:assert(x2:s){f(x2)=x1},
                 focus(z))}}}}}};


//trying ontic approach
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  
  with(f:injection(s,w),
       g:injection(w,s),
       covered_by_g =μ lambda(y:w){
         not(inhabited(preimage(s,w,y,f))) 
         || exists(yy:w){covered_by_g(yy) && y=f(g(yy))}}){
    show(x:s,covered_by_g(f(x))){ //the() safety for defining h()
      inhabited(preimage(w,s,x,g))}{
      with(focus(f(x)), //needed to avoid existence supposition for y:
           y:assert(yy:w){covered_by_g(yy) && f(x)=f(g(yy))}){
        show{is(y,preimage(w,s,x,g))}{
          show{x=g(y)}{with(focus(g(y)))};};}};
    with(uses_g = lambda(x:s){exists(y:preimage(w,s,x,g)){covered_by_g(y)}},
         h = lambda(x:s){if(uses_g(x),
                            the(preimage(w,s,x,g)),
                            f(x))}){
      show(){is(h,injection(s,w))}{
        show(y:w,
             x_2:preimage(s,w,y,h),
             x_3:preimage(s,w,y,h)){
          x_2=x_3}{
          show_case(uses_g(x_2)){
            show{unique(preimage(w,s,x_2,g))}{with(focus(x_2))};
            show{h(x_2)=the(preimage(w,s,x_2,g))};
            show{h(x_2)=y};
            show{covered_by_g(y)};
            show_case(not(uses_g(x_3))){
              
              };
            with(focus(x_2),focus(x_3))
            };
          show_case(not(uses_g(x_2)));}};}}};

//not used below here, obsolete
define inverse(s:set,w:set,f:bijection(s,w)){
  assert(g:bijection(w,s)){
    forall(x:w){f(g(x))=x} &&
    forall(y:s){g(f(y))=y}}};

theorem inverses_exist (s:set, w:set, f:bijection(s,w)){
  inhabited(inverse(s,w,f))}{
  let(g = lambda(x:w){the(y:s){f(y)=x}}){
    lemma{show(is(g,bijection(w,s)))}}
  };
