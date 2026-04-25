
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

break_on_user_error[0] = 1;
/** {42;done} **/

// ========= voodoo block
clear_event(sets_exist);
/** {43;done} **/

//intern_hook[0]=NULL;

// compile new code here

theorem sets_exist (foo:type){inhabited(set_of(foo))}{sorry};
/** {46;done} **/

finish();
/** there is no suspended event to finish **/

// ====== end of voodoo block ====

proof_stepping[0]=1;
/** {47;done} **/

clear_event(emptyset_exists);
/** emptyset_exists has not been defined as an event **/

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
    4.analyzing tau;
    goal not achieved;
    to continue run step(),finish(),or abort_event();} **/

finish();
/** {48;done} **/

int x[0]=0;
/** {49;done} **/

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
/** {50;done} **/

clear_event(preimage);
/** preimage has not been defined as an event **/

define preimage(tau:type, sigma:type, y:sigma, h:tau=>sigma){
  assert(x:tau){h(x)=y}};
/** {51;done} **/

int_exp(max_total[0])
/** {52;1442} **/

clear_event(injection);
/** injection has not been defined as an event **/

define injection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      unique(preimage(y,f))}}};
/** {53;done} **/

//int_exp(intern_hook_count[0])

//event_max_counts()
int_exp(max_total[0])
/** {54;2314} **/

define surjection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    forall(y:sigma){
      inhabited(preimage(y,f))}}};
/** {55;done} **/

int_exp(max_total[0])
/** {56;2143} **/

define bijection(tau:type,sigma:type){
  assert(f:tau=>sigma){
    is(f,injection(tau,sigma)) && is(f,surjection(tau,sigma))}};
/** {57;done} **/

//three versions of bijections_invert. Identical except for the
//injection proof which is modified to exhibit the issue motivating
//congruence on quantified expressions, with the last one requiring the bvars.

int_exp(max_total[0])
/** {58;1842} **/

clear_event(bijections_invert);
/** bijections_invert has not been defined as an event **/

proof_stepping[0]=0;
/** {59;done} **/

theorem bijections_invert(tau:type,sigma:type,inhabited(bijection(tau,sigma))){
  inhabited(bijection(sigma,tau))
  }{
  using(f:bijection(tau,sigma),
        g = lambda(x:sigma){the(y:tau){f(y)=x}}){
    witness(g)
    //show{is(g,injection(sigma,tau))}
    //{show(y:sigma, x1:assert(x:w){g(x)=y}, x2:assert(x:in(w)){g(x)=y}){x1=x2} {show{f(y)=x1}{classify(x1)}; show{f(y)=x2}{classify(x2);};}; classify(g)};
    //show{is(g,surjection(sigma,tau))}
    //{show(x:s){is(f(x), preimage(x,g))};};
    //show{is(g,bijection(w,s))}; 
    }};
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
    8.analyzing tau;
    goal not achieved;
    to continue run step(),finish(),or abort_event();} **/


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
    completed analyzing tau;
    completed analyzing sigma;
    completed analyzing f;
    8.analyzing g;
    goal not achieved;
    to continue run step(),finish(),or abort_event();} **/


types_of(g)
/** {
    60;
    1:pi(bound_x:sigma){
      assert(bound_x_2:tau){
        equal(f(bound_x_2),bound_x)}};
    2:arrow(sigma,[tau@type#0]);
    3:arrow(sigma,tau);} **/

sugar_mvar_subst()
/** {
    61;
    {
      [g@pi(bound_x:sigma){
         assert(bound_x_2:tau){
           equal(f(bound_x_2),bound_x)}}#0];
      [g@arrow(sigma,[tau@type#0])#0];
      [g@arrow(sigma,tau)#0];
      [f@bijection([tau@type#0],[sigma@type#1])#0];
      [sigma@type#1];
      [tau@type#0]}} **/

int_exp(mvar_subst[0]->rest->rest->pair->var->type->upsilon)
/** {63;0} **/

int_exp(intern_exp(`{sigma=>tau})->upsilon)
/** {62;1} **/

why_true(is(g,sigma=>tau))
/** {65;unknown} **/

sugar(signature(intern_exp(`g)))
/** {66;arrow(sigma,tau)} **/

types_of(g)
/** {
    63;
    1:pi(bound_x:sigma){
      assert(bound_x_2:tau){
        equal(f(bound_x_2),bound_x)}};} **/

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
    completed analyzing tau;
    completed analyzing sigma;
    9.analyzing f;
    goal achieved;
    to continue run step(),finish(),or abort_event();} **/


sugar_mvar_subst()
/** {
    84;
    {
      [g@pi(bound_x:sigma){
         assert(bound_x_2:tau){
           equal(f(bound_x_2),bound_x)}}#0];
      [f@bijection([tau@type#0],[sigma@type#1])#0];
      [sigma@type#1];
      [tau@type#0]}} **/

int_exp(truep(intern_exp(`{is(g,bijection(sigma,tau))})))
/** {67;0} **/

clear_query_results();
/** {75;done} **/

types_of(g)
/** {
    82;
    1:pi(bound_x:sigma){
      assert(bound_x_2:tau){
        equal(f(bound_x_2),bound_x)}};} **/

sugar_query_results()
/** {
    77;
    1:bijection(sigma,tau);
    2:pi(bound_x:sigma){
      assert(bound_x_2:tau){
        equal(f(bound_x_2),bound_x)}};} **/

macroexpand(`{types_of(g)})
/** {
    73;
    query_fun(string_atom("g"),
              types_of_enumerator2)} **/



int_exp(item(1)==intern_exp(`{bijection(sigma,tau)}))
/** {61;1} **/

sugar_subst(mvar_subst[0])
/** {
    83;
    {
      [g@pi(bound_x:sigma){
         assert(bound_x_2:tau){
           equal(f(bound_x_2),bound_x)}}#0]-->g;
      [f@bijection([tau@type#0],[sigma@type#1])#0]-->f;
      [sigma@type#1]-->sigma;
      [tau@type#0]-->tau;}} **/

why_true(goal)
/** {
    62;
    {
      truth_of(inhabited(assert(s_bound_x:tau){equal(f(s_bound_x),x)}));
      follows by truth_transfer from;
      1:truth_of(inhabited(preimage(tau,
                                    sigma,
                                    [x@sigma#0],
                                    [f@assert(s_bound_fun:arrow(tau,sigma)){
                                       forall(s_bound_x:sigma){
                                         inhabited(preimage(tau,
                                                            sigma,
                                                            s_bound_x,
                                                            s_bound_fun))}}#0])));
      2:same_find(inhabited(assert(s_bound_x:tau){equal(f(s_bound_x),x)}),
                  inhabited(preimage(tau,
                                     sigma,
                                     [x@sigma#0],
                                     [f@assert(s_bound_fun:arrow(tau,sigma)){
                                        forall(s_bound_x:sigma){
                                          inhabited(preimage(tau,
                                                             sigma,
                                                             s_bound_x,
                                                             s_bound_fun))}}#0])))}} **/

why(1)
/** {
    63;
    {
      truth_of(inhabited(preimage(tau,
                                  sigma,
                                  [x@sigma#0],
                                  [f@assert(s_bound_fun:arrow(tau,sigma)){
                                     forall(s_bound_x:sigma){
                                       inhabited(preimage(tau,
                                                          sigma,
                                                          s_bound_x,
                                                          s_bound_fun))}}#0])));
      follows by forall_mvar_reduct2 from;
      1:truth_of(forall(s_bound_x:sigma){
                   inhabited(preimage(tau,
                                      sigma,
                                      s_bound_x,
                                      [f@assert(s_bound_fun:arrow(tau,sigma)){
                                         forall(s_bound_x:sigma){
                                           inhabited(preimage(tau,
                                                              sigma,
                                                              s_bound_x,
                                                              s_bound_fun))}}#0]))})}} **/

why_true(inhabited(assert(bound_x:tau){equal(f(bound_x),x)}))

class_of(inhabited(assert(bound_x:tau){equal(f(bound_x),x)}))

why_true(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
               equal(f(bound_x_4), bound_x_3)})})

class_of(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
               equal(f(bound_x_4), bound_x_3)})})

sugar(item(1)->arg1)

class_of(assert(bound_x:tau){equal(f(bound_x),[bvar:sigma#0])})


why_true(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
               equal([f@assert(bound_fun:arrow(tau,sigma)){
                           forall(bound_x:sigma){
                             inhabited(assert(bound_x_2:tau){
                                         equal(bound_fun(bound_x_2),
                                               bound_x)})}}#0](bound_x_4), bound_x_3)})})
/**  **/
class_of(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
               equal([f@assert(bound_fun:arrow(tau,sigma)){
                           forall(bound_x:sigma){
                             inhabited(assert(bound_x_2:tau){
                                         equal(bound_fun(bound_x_2),
                                               bound_x)})}}#0](bound_x_4), bound_x_3)})})

notice_safety(intern_exp(`{forall(bound_x_3:sigma){
        inhabited(assert(bound_x_4:tau){
            equal([f@assert(bound_fun:arrow(tau,sigma)){
                  forall(bound_x:sigma){
                    inhabited(assert(bound_x_2:tau){
                        equal(bound_fun(bound_x_2),
                              bound_x)})}}#0](bound_x_4), bound_x_3)})}}));

class_of(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
               equal([f@assert(bound_fun:arrow(tau,sigma)){
                           forall(bound_x:sigma){
                             inhabited(assert(bound_x_2:tau){
                                         equal(bound_fun(bound_x_2),
                                               bound_x)})}}#0](bound_x_4), bound_x_3)})})

why_true(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
               equal(f(bound_x_4), bound_x_3)})})

class_of(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
               equal(f(bound_x_4), bound_x_3)})})

sugar(item(2)->arg1)

int_exp(truep(item(2)->arg2))

int_exp(truep(intern_exp(`{inhabited(assert(bound_x_2:tau){
                                       equal(f(bound_x_2),[x@sigma#0])})})))

int_exp(truep(intern_exp(`{inhabited(assert(bound_x_2:tau){
                                       equal(f(bound_x_2),x)})})))

notice_safety(intern_exp(`{inhabited(assert(bound_x_2:tau){
                                       equal(f(bound_x_2),[x@sigma#0])})})->arg1);

why_true(goal)


//======================================================================

class_of(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
               equal(f(bound_x_4), bound_x_3)})})

sugar(item(1)->arg1)

sugar(item(1)->arg2->arg1->arg1)

mzexp shadow_goal[0]=item(2);

int_exp(uf_equalp(intern_exp(`{[f@assert(bound_fun:arrow(tau,sigma)){
                           forall(bound_x:sigma){
                             inhabited(assert(bound_x_2:tau){
                                         equal(bound_fun(bound_x_2),
                                               bound_x)})}}#0]}),intern_exp(`f)))

why_true(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
                       equal([f@assert(bound_fun:arrow(tau,sigma)){
                                 forall(bound_x:sigma){
                                   inhabited(assert(bound_x_2:tau){
                                               equal(bound_fun(bound_x_2),
                                                     bound_x)})}}#0](bound_x_4), bound_x_3)})})


class_of(forall(bound_x_3:sigma){
           inhabited(assert(bound_x_4:tau){
                       equal([f@assert(bound_fun:arrow(tau,sigma)){
                                 forall(bound_x:sigma){
                                   inhabited(assert(bound_x_2:tau){
                                               equal(bound_fun(bound_x_2),
                                                     bound_x)})}}#0](bound_x_4), bound_x_3)})})


mzexp x[0] = item(1);

mzexp x_shadow[0]=assoc_value(x[0],shadow_alist[0]);

pointer_exp(x_shadow[0])

notice_safety(x[0]);

int_exp(quantifier_constr(x[0]->constructor))

int_exp(!bvarp(x[0]->arg1))

int_exp(every_var(y,x[0]->arg2->freevars){y==x[0]->arg1 || !mvarp(y) || y->binding})

mzexp bvar1[0] = bvar_gensym(type_of(x[0]->arg1),x[0]->subvars);

mzexp shadow_e[0] = intern_from_subst(x[0]->constructor, bvar1[0], substitution(x[0]->arg1,bvar1[0],x[0]->arg2), x[0]);

mzexp shadow_e_find[0] = mz_find(shadow_e[0]);

mzexp xy[0] = make_conservative(x[0],shadow_e_find[0]);

int_exp(truep(xy[0]))

mzexp yx[0] = make_conservative(shadow_e_find[0],x[0]);

int_exp(truep(yx[0]))


sugar(shadow_e[0])

why_true(is(f,surjection(tau,sigma)))

finish();

clear_event(empty_uniqueness);
/** empty_uniqueness has not been defined as an event **/

theorem empty_uniqueness (tau:type) {
  unique(assert(s:set_of(tau)){empty(in(s))})}{
  show(x1:assert(s:set_of(tau)){empty(in(s))},
       x2:assert(s:set_of(tau)){empty(in(s))}){
    x1=x2
      }};

theorem test_injectivity (tau:type,sigma:type,
                          f:injection(tau,sigma), x_2:tau, x_3:tau, f(x_2)=f(x_3)){
  x_2=x_3}{
  classify(f(x_2)); classify(x_3); classify(x_2)};

theorem Schroeder_Bernstein (
                             tau:type,
                             sigma:type,
                             inhabited(injection(tau,sigma)),
                             inhabited(injection(sigma,tau))){
  inhabited(bijection(tau,sigma))}{
  using(f:injection(tau,sigma),
        g:injection(sigma,tau),
	usef =mu assert(x:tau){not(exists(y:sigma){not(is(g(y),usef)) && g(y) = x})}){
    classify(lambda(x:tau){if(is(x,usef),f(x),the(y:sigma){g(y)=x})})}};

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
