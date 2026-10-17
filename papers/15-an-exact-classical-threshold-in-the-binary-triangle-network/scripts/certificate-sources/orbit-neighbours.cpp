#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
// Release portability guard: the frozen format uses little-endian native integers.
#if !defined(__BYTE_ORDER__) || !defined(__ORDER_LITTLE_ENDIAN__)
#error "Use a compiler that reports its native byte order."
#elif __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "This frozen certificate recipe requires a little-endian native target."
#endif

using P=std::array<int,3>;
using Map=std::array<int,27>;
using Lookup=std::array<std::array<uint32_t,256>,4>;
static uint32_t tr(uint32_t v,const Lookup&L){return L[0][v&255]|L[1][(v>>8)&255]|L[2][(v>>16)&255]|L[3][v>>24];}
int main(){
 std::vector<P> ps;P p={0,1,2};do{ps.push_back(p);}while(std::next_permutation(p.begin(),p.end()));
 std::vector<Lookup> group;
 for(auto px:ps)for(auto py:ps)for(auto pz:ps)for(int party=0;party<6;party++){
  Map rv{},rp{},m{};
  for(int x=0;x<3;x++)for(int y=0;y<3;y++){
   rv[3*x+y]=3*px[x]+py[y];
   rv[9+3*x+y]=9+3*px[x]+pz[y];
   rv[18+3*x+y]=18+3*py[x]+pz[y];
  }
  for(int x=0;x<3;x++)for(int y=0;y<3;y++){
   int c=3*x+y,b=9+3*x+y,a=18+3*x+y;
   switch(party){
    case 0:rp[c]=c;rp[b]=b;rp[a]=a;break;
    case 1:rp[a]=18+3*y+x;rp[b]=3*x+y;rp[c]=9+3*x+y;break;
    case 2:rp[a]=9+3*x+y;rp[b]=18+3*x+y;rp[c]=3*y+x;break;
    case 3:rp[a]=3*x+y;rp[b]=18+3*y+x;rp[c]=9+3*y+x;break;
    case 4:rp[a]=9+3*y+x;rp[b]=3*y+x;rp[c]=18+3*x+y;break;
    case 5:rp[a]=3*y+x;rp[b]=9+3*y+x;rp[c]=18+3*y+x;break;
   }
  }
  Lookup L{};
  for(int i=0;i<27;i++)m[i]=rv[rp[i]];
  auto sorted=m;std::sort(sorted.begin(),sorted.end());for(int i=0;i<27;i++)if(sorted[i]!=i)throw std::runtime_error("not permutation");
  for(int byte=0;byte<4;byte++)for(int v=0;v<256;v++)for(int i=0;i<27;i++)if(m[i]/8==byte && (v>>(m[i]%8)&1))L[byte][v]|=1u<<i;
  group.push_back(L);
 }
 std::ifstream in("work/certificates/representatives.bin",std::ios::binary);std::vector<uint32_t> reps(61872);in.read((char*)reps.data(),reps.size()*4);if(!in)throw std::runtime_error("reps");
 const uint32_t N=1u<<27,MASK=N-1;
 std::vector<uint32_t> info(N,~0u);
 for(uint32_t r=0;r<reps.size();r++)for(uint32_t g=0;g<group.size();g++){
  uint32_t w=tr(reps[r],group[g]);
  for(uint32_t flip=0;flip<2;flip++){
   uint32_t z=w^(flip?MASK:0);if(info[z]!=~0u && info[z]>>12!=r)throw std::runtime_error("overlapping reps");
   info[z]=(r<<12)|(g<<1)|flip;
  }
 }
 uint64_t missing=0;for(auto x:info)missing+=x==~0u;if(missing)throw std::runtime_error("missing words");
 std::ofstream out("Paper15/CertificateData/neighbours.bin",std::ios::binary);
 for(uint32_t r=0;r<reps.size();r++){
  out.write((char*)&reps[r],4);
  for(int bit=0;bit<27;bit++){
   uint32_t x=info[reps[r]^(1u<<bit)];uint32_t target=reps[x>>12];uint16_t code=x&4095;
   out.write((char*)&target,4);out.write((char*)&code,2);
  }
 }
 std::cout<<"PASS representatives="<<reps.size()<<" transitions="<<reps.size()*27<<" words="<<N<<" group="<<group.size()*2<<"\n";
}
