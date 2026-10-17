#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
#include <fstream>
#include <boost/multiprecision/cpp_int.hpp>
// Release portability guard: the frozen format uses little-endian native integers.
#if !defined(__BYTE_ORDER__) || !defined(__ORDER_LITTLE_ENDIAN__)
#error "Use a compiler that reports its native byte order."
#elif __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "This frozen certificate recipe requires a little-endian native target."
#endif

using I128=__int128_t;
using I256=boost::multiprecision::int256_t;
constexpr int64_t HNUM=27, HDEN=25;
struct Plane {int64_t a,b,c;};
struct Point {I128 x=0,y=0,d=1;};
struct Bound {I128 n=0,d=1;int plane=-1;bool set=false;};
struct Witness {uint8_t kind=0,j=0,k=0;};
static bool lessfrac(const Bound&a,const Bound&b) {
 return I256(a.n)*I256(b.d)<I256(b.n)*I256(a.d);
}
static bool satisfies(const Plane&a,const Point&p) {
 return I256(a.a)*I256(p.x)+I256(a.b)*I256(p.y)>=I256(a.c)*I256(p.d);
}
static Point intersect(const Plane&a,const Plane&b) {
 Point p;
 p.d=I128(a.a)*b.b-I128(a.b)*b.a;
 p.x=I128(a.c)*b.b-I128(a.b)*b.c;
 p.y=I128(a.a)*b.c-I128(a.c)*b.a;
 if(p.d<0){p.d=-p.d;p.x=-p.x;p.y=-p.y;}
 return p;
}
// Exact feasibility of 27 half planes in two dimensions. A feasible point is
// an exact affine upper certificate for the convex hull of this product cell.
static bool bound_cell(const int64_t F[27][3],int depth,Witness* witness=nullptr) {
 Plane P[27];const int64_t den=int64_t(1)<<depth;
 for(int j=0;j<27;j++) P[j]={HDEN*F[j][0],HDEN*F[j][1],HDEN*F[j][2]-HNUM*den};
 Point p;Witness w;
 for(int j=0;j<27;j++) {
 if(satisfies(P[j],p))continue;
 if(P[j].a==0 && P[j].b==0)return false;
 const bool use_x=P[j].a!=0;
 const int64_t A=use_x?P[j].a:P[j].b;
 const int sign=A>0?1:-1;
 Bound lo,hi;
 for(int k=0;k<j;k++) {
 I128 coefficient, rhs;
 if(use_x){
 coefficient=sign*(I128(P[k].b)*P[j].a-I128(P[k].a)*P[j].b);
 rhs=sign*(I128(P[k].c)*P[j].a-I128(P[k].a)*P[j].c);
 }else{
 coefficient=sign*(I128(P[k].a)*P[j].b-I128(P[k].b)*P[j].a);
 rhs=sign*(I128(P[k].c)*P[j].b-I128(P[k].b)*P[j].c);
 }
 if(coefficient==0){if(rhs>0)return false;continue;}
 Bound q{rhs,coefficient,k,true};
 if(q.d<0){q.d=-q.d;q.n=-q.n;}
 if(coefficient>0){if(!lo.set || lessfrac(lo,q))lo=q;}
 else {if(!hi.set || lessfrac(q,hi))hi=q;}
 }
 if(lo.set && hi.set && lessfrac(hi,lo))return false;
 int active=-1;
 if(lo.set && lo.n>0)active=lo.plane;
 else if(hi.set && hi.n<0)active=hi.plane;
 if(active>=0){p=intersect(P[j],P[active]);
 if(p.d==0)return false;
 w={3,uint8_t(j),uint8_t(active)};}
 else if(use_x){p={P[j].c,0,P[j].a};w={1,uint8_t(j),0};}
 else{p={0,P[j].c,P[j].b};w={2,uint8_t(j),0};}
 if(p.d<0){p.d=-p.d;p.x=-p.x;p.y=-p.y;}
 }
 // Independent final exact check, so a feasibility-algorithm bug cannot
 // create a false pruning decision.
 for(int j=0;j<27;j++) if(!satisfies(P[j],p))return false;
 if(witness)*witness=w;
 return true;
}
struct Cell {
 int64_t F[27][3];
 int64_t V[3][3][3];
 int depths[3]={0,0,0};
 int depth=0;
};
struct Result {int status=0,depth=0;uint64_t nodes=0,leaves=0;};
static int coord(int point,int axis){
 return axis==0?point/9:axis==1?(point/3)%3:point%3;}
static int otherpoint(int point,int axis,int value){
 return point+(value-coord(point,axis))*(axis==0?9:axis==1?3:1);}
static std::array<int,3> split_choice(const Cell&c){
 I128 best=-1;int bestdepth=0;std::array<int,3> out={0,0,1};
 for(int a=0;a<3;a++)for(int i=0;i<3;i++)for(int j=i+1;j<3;j++){
 I128 d=0;
 for(int k=0;k<3;k++){I128 e=c.V[a][i][k]-c.V[a][j][k];d+=e*e;}
 if(best<0 || (I256(d)<<(2*bestdepth))>
 (I256(best)<<(2*c.depths[a]))){best=d;
 bestdepth=c.depths[a];
 out={a,i,j};}
 }
 return out;
}
static Cell child(const Cell&c,int axis,int replaced,int other){
 Cell d=c;d.depth++;d.depths[axis]++;
 for(int p=0;p<27;p++)for(int k=0;k<3;k++)
 d.F[p][k]=coord(p,axis)==replaced?
 c.F[p][k]+c.F[otherpoint(p,axis,other)][k]:
 2*c.F[p][k];
 for(int i=0;i<3;i++)for(int k=0;k<3;k++)
 d.V[axis][i][k]=i==replaced?
 c.V[axis][i][k]+c.V[axis][other][k]:
 2*c.V[axis][i][k];
 return d;
}
static Cell root(uint32_t pattern){
 Cell c{};
 for(int a=0;a<3;a++)for(int i=0;i<3;i++)c.V[a][i][i]=1;
 for(int i=0;i<3;i++)for(int j=0;j<3;j++)for(int k=0;k<3;k++){
 const int z=1-2*int((pattern>>(i*3+j))&1u);
 const int y=1-2*int((pattern>>(9+i*3+k))&1u);
 const int x=1-2*int((pattern>>(18+j*3+k))&1u);
 int p=i*9+j*3+k;
 c.F[p][0]=x+y+z;c.F[p][1]=x*y*z;c.F[p][2]=x*y+y*z+z*x;
 }
 return c;
}
static std::vector<uint8_t> proof_trace;
static Result verify_pattern(uint32_t pattern,uint64_t limit,int maxdepth){
 proof_trace.clear();
 std::vector<Cell> todo;todo.push_back(root(pattern));Result r;
 while(!todo.empty()){
 Cell c=todo.back();todo.pop_back();
 r.nodes++;
 r.depth=std::max(r.depth,c.depth);
 Witness w;
 if(bound_cell(c.F,c.depth,&w)){
 proof_trace.push_back(uint8_t(128+w.kind));
 proof_trace.push_back(w.j); proof_trace.push_back(w.k);
 r.leaves++;
 continue;
 }
 if(r.nodes>=limit){r.status=1;return r;}
 if(c.depth>=maxdepth){r.status=2;return r;}
 auto s=split_choice(c);
 proof_trace.push_back(uint8_t(s[0]));
 proof_trace.push_back(uint8_t(s[1])); proof_trace.push_back(uint8_t(s[2]));
 // Prefix order: the child replacing the lower-numbered vertex first.
 todo.push_back(child(c,s[0],s[2],s[1]));
 todo.push_back(child(c,s[0],s[1],s[2]));
 }
 return r;
}

using Perm=std::array<int,3>;
using Lookup=std::array<std::array<uint32_t,256>,4>;
constexpr uint32_t N=uint32_t(1)<<27, MASK=N-1;
void require(bool ok) {
 if(!ok) throw std::runtime_error("verification failed");
}
int edge(int a,int i,int b,int j) {
 if(a>b){std::swap(a,b);std::swap(i,j);}
 int block=(a==0 ? (b==1 ? 0 : 1) : 2);
 return 9*block+3*i+j;
}
std::vector<Lookup> symmetries() {
 std::vector<Perm> ps;
 Perm p={0,1,2};
 do {ps.push_back(p);} while(std::next_permutation(p.begin(),p.end()));
 std::vector<Lookup> out;
 uint64_t fixed=0;
 for(auto parts:ps) for(auto p0:ps)
 for(auto p1:ps) for(auto p2:ps) {
 Perm m[3]={p0,p1,p2};
 std::array<int,27> image;
 for(int a=0;a<3;a++) for(int b=a+1;b<3;b++)
 for(int i=0;i<3;i++) for(int j=0;j<3;j++)
 image[edge(a,i,b,j)]=edge(parts[a],m[a][i],parts[b],m[b][j]);
 bool visited[27]={}; int cycles=0;
 for(int i=0;i<27;i++) if(!visited[i]) {
 cycles++;
 for(int j=i;!visited[j];j=image[j]) visited[j]=true;
 }
 fixed+=uint64_t(1)<<cycles;
 Lookup L{};
 for(int byte=0;byte<4;byte++) for(int v=0;v<256;v++)
 for(int bit=0;bit<8 && 8*byte+bit<27;bit++)
 if((v>>bit)&1) L[byte][v]|=uint32_t(1)<<image[8*byte+bit];
 out.push_back(L);
 }
 require(out.size()==1296 && fixed==160372224);
 return out;
}
uint32_t transform(uint32_t v,const Lookup& L) {
 return L[0][v&255]|L[1][(v>>8)&255]|
 L[2][(v>>16)&255]|L[3][v>>24];
}
int main() {
 std::ofstream forest("work/certificates/forest.bin",std::ios::binary);
 std::ofstream reps("work/certificates/representatives.bin",std::ios::binary);
 require(bool(forest) && bool(reps));
 auto group=symmetries();
 uint32_t reference=0;
 for(int block=0;block<3;block++)
 for(int i=0;i<3;i++) for(int j=0;j<3;j++) {
 bool positive=(i==0 && j==1)||(i==1 && j==0)||(i==1 && j==1);
 if(!positive) reference|=uint32_t(1)<<(9*block+3*i+j);
 }
 uint32_t exceptional=MASK;
 for(const auto& L:group) {
 uint32_t w=transform(reference,L);
 exceptional=std::min(exceptional,std::min(w,MASK^w));
 }
 require(reference==127388645 && exceptional==2889227);
 std::vector<uint64_t> seen(N/64,0);
 uint64_t orbits=0,certified=0,nodes=0,leaves=0;
 int depth=0;
 for(uint32_t v=0;v<N;v++) {
 if((seen[v/64]>>(v%64))&1) continue;
 orbits++;
 reps.write(reinterpret_cast<const char*>(&v),sizeof(v));
 for(const auto& L:group) {
 uint32_t w=transform(v,L), z=MASK^w;
 seen[w/64]|=uint64_t(1)<<(w%64);
 seen[z/64]|=uint64_t(1)<<(z%64);
 }
 if(v==exceptional) continue;
 Result r=verify_pattern(v,2000000,42);
 require(r.status==0);
 require(proof_trace.size()==3*r.nodes);
 forest.write(reinterpret_cast<const char*>(&v),sizeof(v));
 forest.write(reinterpret_cast<const char*>(&r.nodes),sizeof(r.nodes));
 forest.write(reinterpret_cast<const char*>(proof_trace.data()),proof_trace.size());
 require(bool(forest) && bool(reps));
 certified++; nodes+=r.nodes; leaves+=r.leaves;
 depth=std::max(depth,r.depth);
 if(certified%5000==0) std::cerr<<certified<<" cases checked\n";
 }
 require(orbits==61872 && certified==61871);
 require(nodes==5103027 && leaves==2582449 && depth==27);
 require(nodes==2*leaves-certified);
 std::cout<<"PASS orbits="<<orbits<<" certified="<<certified
 <<" nodes="<<nodes<<" leaves="<<leaves
 <<" depth="<<depth<<"\n";
}
