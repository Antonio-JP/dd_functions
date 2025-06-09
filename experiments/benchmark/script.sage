
from sys import path
path.insert(0,"../..") # dd_functions is here

from csv import writer
from datetime import datetime
from time import perf_counter
from dd_functions.dd_functions.ddExamples import *

def experiment_tan_derivative():
    t = Tan(x)
    if t.derivative() != (1 + t^2):
        raise ValueError("Tan derivative test failed")
    
def experiment_tan_cos():
    t = Tan(x)
    c = Cos(x)
    
    if t * c != Sin(x):
        raise ValueError("Tan composition with Cos test failed")
    
def experiment_triple_sine():
    s = Sin(x)
    
    sss = s(s(s))
    if sss.sequence(10, True) != [0, 1, 0, -1/2, 0, 11/40, 0, -731/5040, 0, 2873/40320]:
        raise ValueError("Triple sine sequence test failed")
    
def experiment_mathieu():
    raise ValueError("Mathieu functions are not implemented yet")
    # w1 = Mathieu('a','q',(1,0))
    # w2 = Mathieu('a','q',(0,1))

    # w1d = w1.derivative()
    # w2d = w2.derivative()

    # if w1*w2d - w2*w1d != 1:
    #     raise ValueError("Mathieu derivative test failed")

def experiment_bessel():
    f = BesselJ(3)(Sin(x)) - BesselJ(2)(Cos(x)-1)
    if f.sequence(10, True) != [0,0,0, 1/48, -1/32, -3/256, 1/192, 311/92160, 1/3840, -6845/9289728]:
        raise ValueError("Bessel function sequence test failed")

def experiment_polylog():
    f = Polylogarithm(2)(Exp(x)-1) + Tan(x)
    if f.init(6, True) != [0, 2, 3/2, 31/6, 10, 1829/30]:
        raise ValueError("Polylogarithm function test failed")
    
def experiment_hypergeometric():
    f = HypergeometricFunction()(Sin(x))

def experiment_hypergeometric_2():
    f = HypergeometricFunction(1, 2, 3)(HypergeometricFunction(1,2,3)-1)
    if f.init(10, True) != [1, 4/9, 10/9, 194/45, 9199/405, 429056/2835, 691916/567, 631779176/54675, 763773224/6075, 3615884017376/2338875]:
        raise ValueError("Hypergeometric function test failed")
    
def experiment_elliptic_legendre():
    f = EllipticLegendreD(1) - EllipticLegendreD(2)

def experiment_fibonacci():
    FibonacciD()(FibonacciD((0,'a')))

EXPERIMENTS = [experiment_tan_derivative, experiment_tan_cos, experiment_triple_sine, experiment_mathieu, experiment_bessel,
               experiment_polylog, experiment_hypergeometric, experiment_hypergeometric_2, experiment_elliptic_legendre, experiment_fibonacci]

def run_experiments(date, version, csv_writer):
    results = []
    for func in EXPERIMENTS:
        try:
            start_time = perf_counter()
            func()
            end_time = perf_counter()
            elapsed_time = end_time - start_time
        except Exception as e:
            print(f"Error running {func.__name__}: {e}")
            elapsed_time = "Error"
        results.append(elapsed_time)

    csv_writer.writerow([date, version] + results)
        
if __name__ == "__main__":
    with open("../../VERSION", "r") as version_file:
        version = version_file.read().strip()
    date = datetime.now().strftime('%Y/%m/%d %H:%M:%S')

    with open("results.csv", "a+") as result_file:
        csv_writer = writer(result_file, delimiter=";")

        run_experiments(date, version, csv_writer)