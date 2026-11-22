/* Optional strict-IEEE acceleration of the same rounded stencil and RNG tape.
 * Binary64 intermediates; no fast math or fused operations. The random callback
 * is NumPy's bit-generator C next_double, never a Python callback. */
#include <stdint.h>
#include <math.h>
#include <string.h>
#include <stddef.h>

typedef double (*random_double)(void *);
typedef struct {
    int emin,remove;
    uint64_t mask,half;
    double fractional_scale,maximum,step,inverse_step,tiny;
} Format;

static Format format(int p,int emin,int emax) {
    Format f;
    f.emin=emin; f.remove=53-p;
    f.mask=(UINT64_C(1)<<f.remove)-1;
    f.half=UINT64_C(1)<<(f.remove-1);
    f.fractional_scale=ldexp(1.,-f.remove);
    f.maximum=ldexp(2.0-ldexp(1.,1-p),emax);
    f.step=ldexp(1.,emin-p+1);
    f.inverse_step=ldexp(1.,p-1-emin);
    f.tiny=ldexp(1.,emin);
    return f;
}

static uint64_t bits(double x) { uint64_t u; memcpy(&u,&x,8); return u; }
static double number(uint64_t u) { double x; memcpy(&x,&u,8); return x; }

static double rounded(double x, const Format *f, int sr, double u) {
    if (!isfinite(x)) return x;
    uint64_t b=bits(x), sign=b&UINT64_C(0x8000000000000000);
    uint64_t a=b&UINT64_C(0x7fffffffffffffff);
    int exponent=(int)(a>>52)-1023;
    double answer;
    if (exponent>=f->emin) {
        uint64_t lower=a&~f->mask, remainder=a&f->mask;
        uint64_t increment;
        if (sr) {
            double fraction=(double)remainder*f->fractional_scale;
            increment=sign ? u>=1.0-fraction : u<fraction;
        } else {
            increment=remainder>f->half || (remainder==f->half && ((lower>>f->remove)&1));
        }
        answer=number(sign|(lower+(increment<<f->remove)));
    } else {
        double scaled=x*f->inverse_step;
        if (sr) {
            double lower=floor(scaled);
            answer=(lower+(u<scaled-lower))*f->step;
        } else {
            answer=nearbyint(scaled)*f->step;
        }
    }
    return fabs(answer)>f->maximum ? copysign(INFINITY,answer) : answer;
}

/* Inputs first, then the exact multiplication by four. Its random slot is
 * skipped with PCG.advance in Python, preserving the subsequent tape. */
void lp_inputs(const double *x,double *q,double *v,size_t count,int p,int emin,int emax,
               int sr,void *state,random_double random) {
    Format f=format(p,emin,emax);
    for (size_t i=0;i<count;i++) q[i]=rounded(x[i],&f,sr,sr?random(state):0.);
    for (size_t i=0;i<count;i++) {
        double value=4.*q[i];
        v[i]=fabs(value)>f.maximum ? copysign(INFINITY,value) : value;
    }
}

/* Four complete row-major passes match the four NumPy random-array requests. */
int lp_finish(const double *q,double *v,double *out,size_t n,int p,int emin,int emax,
               int sr,void *state,random_double random) {
    size_t count=n*n;
    Format f=format(p,emin,emax);
    for (int direction=0;direction<4;direction++) {
        for (size_t i=0;i<count;i++) {
            size_t row=i/n,col=i%n;
            double neighbour=0.;
            if (direction==0 && row>0) neighbour=q[i-n];
            if (direction==1 && row+1<n) neighbour=q[i+n];
            if (direction==2 && col>0) neighbour=q[i-1];
            if (direction==3 && col+1<n) neighbour=q[i+1];
            double value=v[i]-neighbour;
            v[i]=rounded(value,&f,sr,sr?random(state):0.);
        }
    }
    int needs_rounding=0;
    for (size_t i=0;i<count;i++) {
        out[i]=v[i]*.125;
        if (out[i]!=0. && fabs(out[i])<f.tiny) needs_rounding=1;
    }
    /* Normal scaling by a power of two is exact. No later draw uses this
     * call's generator; an unused final operation need not advance its tape. */
    if (needs_rounding) for (size_t i=0;i<count;i++)
        out[i]=rounded(out[i],&f,sr,sr?random(state):0.);
    return needs_rounding;
}
