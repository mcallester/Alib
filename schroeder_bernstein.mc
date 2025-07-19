
restart_event(`schroeder_bernstein);

declare_package(`schroeder_bernstein);

class function(){domain:set, range:set, op:arrow(domain,range)};

define injective_arrow(domain:set, range:set){
  assert(op:arrow(domain,range)){
    forall(y:range){
      unique(assert(x:domain){y = op(x)})}}};

define injection{
  assert(f:function){
    is(op, injective_arrow(domain,range))}};

class injective_function(function){is(op,injective_arrow(domain,range))};

theorem injective_functions_are_functions(f:injective_function){is(f,function)};

define surjective_arrow(domain:set, range:set){
  assert(op:arrow(domain,range)){
    forall(y:range){
      exists(x:domain){op(x)=y}}}};

define surjection{
  assert(f:function){
    is(op, surjective_arrow(domain,range))}};

define bijective_arrow(domain:set, range:set){
  assert(op:arrow(domain,range)){
    is(op,injective_arrow(domain,range)) &&
    is(op,surjective_arrow(domain,range))}};

define bijection{
  assert(f:function){
    is(f,injection) && is(f,surjection)}};

define inverse(f:bijection){
  obj(function,domain=f.range, range=f.domain, op = lambda(x:f.range){the(y:f.domain){(f.op)(y)=x}})
};
theorem inverses_are_functions(f:bijection){is(inverse(f),function)};

theorem bijections_invert (f:bijection) {is(inverse(f),bijection)}{
  show(is(inverse(f),surjection)){
    show(is(inverse(f),function));
    show(is(inverse(f).op,surjective_arrow(f.range, f.domain)));
    show(f.domain = inverse(f).range);
    show(f.range = inverse(f).domain);
    show(surjective_arrow(f.range, f.domain)=surjective_arrow(inverse(f).domain, inverse(f).domain));
    show(is(inverse(f).op,surjective_arrow(inverse(f).domain, inverse(f).domain)))
    };
  };

truth_of(f.domain=inverse(f).range)

truth_of(f.range=inverse(f).domain)

truth_of(surjective_arrow(inverse(f).domain, inverse(f).domain) = surjective_arrow(f.range, f.domain))

nil;

//break_on_throw_event[0]=1;

theorem Schroeder_Bernstein (funpair:class(function){
                               op2:arrow(range,domain),
                               is(op,injective_arrow(domain,range)),
                               is(op2,injective_arrow(range,domain))}) {
  inhabited(bijective_arrow(domain,range))}{
  let(f=op,
      g=op2,
      s=domain,
      w=range,
      use_f =μ lambda(x:s){
        not(exists(y:w){
              g(y)=x
              && not(exists(z:s){
                       f(z)=y && use_f(z)})})},
      h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
    show(is(h,surjective_arrow(s,w))){
      lemma{
        let(x1:w){
          show(exists(x2:s){h(x2)=x1}){
            /* let(z:assert(z:s){f(z)=x1 && use_f(z)}) */
            suppose(use_f(g(x1))){
              consider(g(x1),assert(x2:s){f(x2)=x1})}
            /* { */
              /*   suppose(use_f(g(x1))){ */
                /*     show(exists(z:s){f(z)=x1 && use_f(z)})} */
              /*   } */
            }
          }}}}};
