// Exhaustive exact composition on the 65,536 local truth tables.
// Recovered from the 2026-10-03 computational bundle; see README.md.
#ifdef NDEBUG
#error "Compile with assertions enabled: omit -DNDEBUG."
#endif
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>

using Map = std::array<uint8_t,16>;
std::array<Map,65536> maps;
int shift(int x, int g) {
    int y=0;
    for (int h=0;h<4;++h) y |= ((x>>(h^g))&1)<<h;
    return y;
}
int compose(int outer, int inner) {
    int result=0;
    for (int x=0;x<16;++x) result |= ((outer>>maps[inner][x])&1)<<x;
    return result;
}
bool invariant(int f) {
    if (maps[f][0]==maps[f][15]) return true;
    for (int x=0;x<16;++x) if (__builtin_popcount(x)%2)
        for (int y=x+1;y<16;++y) if (__builtin_popcount(y)%2)
            if (maps[f][x]==maps[f][y] && __builtin_popcount(maps[f][x])%2) return false;
    return true;
}
struct Closure {
    std::array<int,65536> previous, generator, depth;
    std::vector<int> queue;
};
Closure compute(const std::vector<int>& generators, int identity, const std::string& stem) {
    Closure c;
    c.previous.fill(-2); c.generator.fill(-1); c.depth.fill(-1);
    c.previous[identity]=-1; c.depth[identity]=0; c.queue.push_back(identity);
    for (size_t head=0;head<c.queue.size();++head) {
        int f=c.queue[head];
        for (int gen:generators) {
            int h=compose(gen,f);
            if (c.previous[h]!=-2) continue;
            c.previous[h]=f; c.generator[h]=gen; c.depth[h]=c.depth[f]+1;
            c.queue.push_back(h);
        }
    }
    std::ofstream table(stem+"-membership.csv");
    table.exceptions(std::ios::failbit | std::ios::badbit);
    table<<"rule_id,member,shortest_length,predecessor_rule,generator_rule,application_order_generator_word\n";
    for (int f=0;f<65536;++f) {
        std::vector<int> word;
        if (c.depth[f]>=0) {
            for (int v=f;c.previous[v]>=0;v=c.previous[v]) word.push_back(c.generator[v]);
            std::reverse(word.begin(),word.end());
            int replay=identity;
            for (int gen:word) replay=compose(gen,replay);
            assert(replay==f);
        }
        table<<f<<','<<(c.depth[f]>=0)<<','<<c.depth[f]<<','<<c.previous[f]<<','<<c.generator[f]<<",\"";
        for (size_t i=0;i<word.size();++i) table<<(i?" ":"")<<word[i];
        table<<"\"\n";
    }
    table.close();
    int maxdepth=0;
    for (int f:c.queue) maxdepth=std::max(maxdepth,c.depth[f]);
    std::cout<<stem<<": size="<<c.queue.size()<<", max_shortest_length="<<maxdepth<<"\n";
    std::vector<int> histogram(maxdepth+1,0);
    for (int f:c.queue) ++histogram[c.depth[f]];
    std::cout<<stem<<": length_distribution=";
    for (size_t k=0;k<histogram.size();++k) std::cout<<(k?" ":"")<<histogram[k];
    std::cout<<'\n';
    return c;
}
int main() {
    int identity=0;
    for (int x=0;x<16;++x) identity |= (x&1)<<x;
    std::vector<int> units;
    for (int rule=0;rule<65536;++rule) {
        std::set<int> images;
        for (int x=0;x<16;++x) {
            int out=0;
            for (int g=0;g<4;++g) out |= ((rule>>shift(x,g))&1)<<g;
            maps[rule][x]=out;
            images.insert(out);
        }
        for (int x=0;x<16;++x) for (int g=0;g<4;++g)
            assert(maps[rule][shift(x,g)]==shift(maps[rule][x],g));
        if (images.size()==16) units.push_back(rule);
    }
    assert(units.size()==512);
    std::set<int> lazyset;
    std::ofstream definitions("lazy-generators.csv");
    definitions.exceptions(std::ios::failbit | std::ios::badbit);
    definitions<<"neighborhood_mask,active_pattern_bits,rule_id\n";
    for (int neighborhood=1;neighborhood<16;neighborhood+=2) {
        for (int pattern=0;pattern<16;++pattern) if ((pattern&~neighborhood)==0) {
            int rule=identity;
            for (int x=0;x<16;++x) if ((x&neighborhood)==pattern) rule ^= 1<<x;
            lazyset.insert(rule);
            definitions<<neighborhood<<','<<pattern<<','<<rule<<'\n';
        }
    }
    definitions.close();
    assert(lazyset.size()==54);
    std::vector<int> lazy(lazyset.begin(),lazyset.end());
    std::vector<int> both=lazy;
    both.insert(both.end(),units.begin(),units.end());
    std::sort(both.begin(),both.end());
    both.erase(std::unique(both.begin(),both.end()),both.end());
    auto L=compute(lazy,identity,"lazy");
    auto M=compute(both,identity,"units-lazy");
    int invariant_count=0, invariant_missing=0, invariant_violations=0;
    for (int f=0;f<65536;++f) {
        bool valid=invariant(f);
        invariant_count += valid;
        invariant_missing += valid && M.depth[f]<0;
        invariant_violations += !valid && M.depth[f]>=0;
        assert(L.depth[f]<0 || M.depth[f]>=0);
        assert(M.depth[f]<0 || valid);
    }
    // Does the identity already occur in a nonempty lazy word? This settles
    // semigroup-versus-monoid conventions without adding an extra element.
    bool identity_in_nonempty_lazy=false;
    for (int f:L.queue) for (int gen:lazy) if (compose(gen,f)==identity) identity_in_nonempty_lazy=true;
    int witness=0;
    for (int x=0;x<16;++x) witness |= ((__builtin_popcount(x)==1 ? 1-(x&1) : x&1))<<x;
    assert(M.depth[witness]<0);
    std::ofstream report("closure-summary.json");
    report.exceptions(std::ios::failbit | std::ios::badbit);
    report<<"{\n  \"cell_order\": [\"e\",\"a\",\"b\",\"ab\"],\n"
          <<"  \"rule_encoding\": \"bit x of rule is the output at e on configuration x; cell e is bit0\",\n"
          <<"  \"CA_count\": 65536,\n  \"unit_count\": "<<units.size()<<",\n"
          <<"  \"lazy_generator_count\": "<<lazy.size()<<",\n"
          <<"  \"lazy_closure_count\": "<<L.queue.size()<<",\n"
          <<"  \"units_lazy_closure_count\": "<<M.queue.size()<<",\n"
          <<"  \"invariant_satisfying_count\": "<<invariant_count<<",\n"
          <<"  \"invariant_satisfying_outside_units_lazy\": "<<invariant_missing<<",\n"
          <<"  \"invariant_violating_inside_units_lazy\": "<<invariant_violations<<",\n"
          <<"  \"identity_in_nonempty_lazy_closure\": "<<(identity_in_nonempty_lazy?"true":"false")<<",\n"
          <<"  \"counterexample_rule\": "<<witness<<",\n"
          <<"  \"formalization\": \"No new Lean run; finite enumeration and replay certificates only\"\n}\n";
    report.close();
    std::cout<<"Invariant: "<<invariant_count<<"; missing="<<invariant_missing
             <<"; violations="<<invariant_violations<<"; identity nonempty="<<identity_in_nonempty_lazy<<"\n";
}
