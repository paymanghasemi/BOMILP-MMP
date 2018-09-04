/* 
 * File:   main.cpp
 * Author: Payman Ghasemi Saghand
 */




/*
 * Branching =1 is random branching
 * Branching =2 is reliability branching
 * Branching =3 is most infeasible branching
 * Branching =4 is Pseudocosts random branching
 * Branching =5 is Pseudocosts most infeasible branching
 * Noding =1 is best-bound noding
 * Noding =2 is depth-first noding
 * Noding =3 is two-phase noding method
 * Noding =4 is best expected bound noding
 * Noding =5 is best estimate noding 
 */

#include <cstdlib>
#include <iostream>
#include <fstream>
#include <ilcplex/ilocplex.h>
#include <sys/time.h>
#include <ctime>
#include <vector> 
#include <math.h>
#include <stdlib.h>
#include <stdio.h> 

using namespace std;

/*Define constant values*/

#define Positive_infinity 100000000
#define Negative_infinity -100000000
#define Abs_Optimal_Tol 1.0e-6
#define Rel_Optimal_Tol 1.0e-6
#define epsilon 1.0e-6
#define denominator 1.0e-20
#define Cplex_Gap 1.0e-6
#define T_Limit 7200
#define Strong_mu 0.9
#define threshold 2
#define cut_epsilon 1.0e-7
#define Output_presicion 10

#define ClearFunctions

double Global_LB(Negative_infinity);
double Global_UB(Positive_infinity);
int Number_of_Explored_Nodes = 0;
double* Best_Solution;
double RHS;
int Index;
bool SSign;
char* LP_file_name;
char* IP_file_name;
double N_Objectives;
double* Solution;
int p = 2;
int N_Variables;
double zu1;
double zu2;
double zl1;
double zl2;
double Cutting_Plane_Value;
double zlast1;
double zlast2;
int Search;
double vzu;
double vy;
double Check_Value;
double Intpart;
double Fracpart;
bool Infeasibility;
double bestnode;
bool It_is_Added;
struct timeval startTime, endTime;
double clock_Run_time(0);
double clock_start_time;
int Noding;
int Branching;
double* p_minus;
double* p_plus;
double* n_minus;
double* n_plus;
double* D_minus;
double* D_plus;
double si;
double si_temp;
double UB_temp;
int* Type;
double ZI[3];
double b_plus;
double b_minus;
bool Node_Index_Added;
int Number_of_Constraints;
int Number_of_LPs = 0;
int Open_Nodes;
bool Primal_Optimality = 0;
double Primal_Solution;
int Number_of_Infeasibles = 0;
int Pruned = 0;
bool Primal_search;
bool Primal_Cut_Add;
double Prime_time = 0;
double Prime_start;
double Prime_run;
double lambda_sum;
int Node_Index_Temp;
int Next_Branch;
bool Optimality = 0;
double bandb_time;
double bandb_start;
double bandb_run;
double bandb_loop_start;
double bandb_loop_run;
int Psuedocost_counter = 0;
bool Optimal_checker;
double Primal_time;
int Random_index;
int Fr_index;
bool Skip = 0;
bool Mixed_integer = 0;

ILOSTLBEGIN
IloEnv env;
IloModel model(env);
IloRangeArray Constraints(env);
IloSOS1Array sos1(env);
IloSOS2Array sos2(env);
IloNumVarArray var_x(env);
IloObjective object(env);
IloCplex cplex(env);
IloModel Intmodel(env);
IloModel Primal_model(env);
IloCplex Primal_cplex(Primal_model);
IloObjective Primal_Obj(env);
IloRangeArray Primal_Constraints(env);
IloSOS1Array Intsos1(env);
IloSOS2Array Intsos2(env);
IloNumVarArray Primal_x(env);
IloObjective Intobject(env);
IloCplex Intcplex(env);
IloModel lp_model1(env);
IloCplex lp_cplex1(lp_model1);
IloObjective Objective1(env);
IloModel lp_model2(env);
IloCplex lp_cplex2(lp_model2);
IloObjective Objective2(env);
IloExpr Math(env);
IloExpr Obj1(env);
IloExpr Obj2(env);
IloExpr ZlObj(env);
IloRangeArray Intersection_Constraint(env);
IloRangeArray Cutting_Plane(env);
IloRangeArray Cutting_Plane_Obj(env);
IloModel Zl_model(env);
IloCplex Zl_cplex(Zl_model);
IloObjective Zl_Obj(env);
IloModel Check_model(env);
IloCplex Check_cplex(Check_model);
IloObjective Check_Obj(env);
IloRangeArray BandB_Constraints(env);
IloRangeArray Strong(env);

void Getting_Integers() {
    Intcplex.importModel(Intmodel, IP_file_name, Intobject, Primal_x, Primal_Constraints, Intsos1, Intsos2);
    cplex.importModel(model, LP_file_name, object, var_x, Constraints, sos1, sos2);
    N_Variables = Primal_x.getSize();
    Type = new int [N_Variables];
    Solution = new double [N_Variables];
    Best_Solution = new double [N_Variables];
    p_minus = new double [N_Variables];
    p_plus = new double [N_Variables];
    n_minus = new double [N_Variables];
    n_plus = new double [N_Variables];
    D_minus = new double [N_Variables];
    D_plus = new double [N_Variables];
    Math.clear();
    Obj1.clear();
    Obj2.clear();
    cplex.end();
    Intcplex.end();
    Obj1 = Constraints[0].getExpr();
    Obj2 = Constraints[1].getExpr();
    Intmodel.remove(Primal_Constraints);
    Intmodel.remove(Intobject);
    Intmodel.end();
    Intobject.end();
    model.remove(Constraints);
    model.remove(object);
    model.end();
    Constraints.remove(0);
    Constraints.remove(0);
    Primal_Constraints.remove(0);
    Primal_Constraints.remove(0);
    Objective1 = IloMaximize(env, Obj1);
    Objective2 = IloMaximize(env, Obj2);
    Zl_Obj = IloMaximize(env, Obj1 + Obj2);

    for (int i = 0; i < N_Variables; i++) {
        p_minus[i] = 0.0;
        p_plus[i] = 0.0;
        n_minus[i] = 0.0;
        n_plus[i] = 0.0;
        D_minus[i] = 0.0;
        D_plus[i] = 0.0;
        Type[i] = Primal_x[i].getType();
        if (Type[i] == 3) {
            Constraints.add(var_x[i] <= 1);
            Constraints.add(var_x[i] >= 0);
        }
    }

    Number_of_Constraints = Primal_Constraints.getSize() - 2;

    lp_model1.add(Objective1);
    lp_model1.add(Constraints);
    lp_model2.add(Objective2);
    lp_model2.add(Constraints);
    Zl_model.add(Constraints);
    Zl_model.add(Zl_Obj);
    Check_model.add(Constraints);
    Primal_model.add(Primal_Constraints);
}

void Writing_The_Output_File() {
    ofstream OutputFile;
    OutputFile.open("Output.txt", ios::app);

    OutputFile << IP_file_name << " GLB= " << std::setprecision(Output_presicion) << Global_LB << " GUB= " << Global_UB <<" Gap= "<< (Global_UB-Global_LB)/(Global_UB+epsilon) << " #Var= " << N_Variables - 2 << " #Constraints= " << Number_of_Constraints << " Nodes= " << Number_of_Explored_Nodes << " #LP= " << Number_of_LPs << " Open_Nodes= " << Open_Nodes;
    if (Primal_search == 1) {
        OutputFile << " Time= " << (clock_Run_time / CLOCKS_PER_SEC) + Primal_time;
        if (Optimality == 1) {
            if (Global_LB <= Primal_Solution + epsilon && Global_LB >= Primal_Solution - epsilon) {
                Primal_Optimality = 1;
            }
            OutputFile << " Primal_Optimality= " << Primal_Optimality;
        }
    } else {
        OutputFile << " Time= " << (clock_Run_time / CLOCKS_PER_SEC);
    }
    OutputFile << " #Inf_Nodes= " << Number_of_Infeasibles << " #Pruned_Nodes= " << Pruned << endl;
    OutputFile.close();
}

double Constraint_Modifier(double RHS) {
    double Modifier;
    Modifier = epsilon * (RHS + 1);
    return Modifier;
}

class Prime {
public:
    double** y;
    double* lambda;
    double* Next_y;
    bool Useful;

    Prime() {
        y = new double* [3];
        lambda = new double [3];
        Next_y = new double [2];
        for (int i = 0; i < 3; i++) {
            y[i] = new double [3];
        }
        lambda[1] = 0;
        lambda[2] = 0;
        Useful = 0;
    }

    void Initialize_Prime(Prime* Parent, int pointer) {
        y[1][1] = Parent->y[pointer][1];
        y[1][2] = Parent->y[pointer][2];
        y[2][1] = Parent->Next_y[1];
        y[2][2] = Parent->Next_y[2];
    }

    void Explore_Prime() {
        lambda[1] = y[1][2] - y[2][2];
        lambda[2] = y[2][1] - y[1][1];
        lambda_sum = lambda[1] + lambda[2];
        lambda[1] = (lambda[1]) / (lambda_sum);
        lambda[2] = (lambda[2]) / (lambda_sum);
        Primal_Obj = IloMinimize(env, -(lambda[1] * Primal_x[0]) - (lambda[2] * Primal_x[1]));
        Primal_model.add(Primal_Obj);
        Primal_cplex.extract(Primal_model);
        Primal_cplex.setParam(IloCplex::Threads, 1);
        Primal_cplex.setParam(IloCplex::TiLim, Prime_time);
        Primal_cplex.setParam(IloCplex::EpGap, Cplex_Gap);
        Primal_cplex.setOut(env.getNullStream());
        Number_of_LPs++;
        Prime_start = clock();
        if (Primal_cplex.solve() && Primal_cplex.getMIPRelativeGap() <= Cplex_Gap) {
            if (Primal_cplex.getValue(Primal_x[0]) * Primal_cplex.getValue(Primal_x[1]) > Global_LB) {
                for (int i = 0; i < N_Variables; i++) {
                    Best_Solution[i] = Primal_cplex.getValue(Primal_x[i]);
                }
                Global_LB = Best_Solution[0] * Best_Solution[1];
                Primal_Solution = Global_LB;
            }
            if (Primal_Cut_Add == 1) {
                lp_model1.add(lambda[1] * Obj1 + lambda[2] * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
                lp_model2.add(lambda[1] * Obj1 + lambda[2] * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
                Zl_model.add(lambda[1] * Obj1 + lambda[2] * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
                Check_model.add(lambda[1] * Obj1 + lambda[2] * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
            }
            if ((-Primal_cplex.getObjValue() > lambda[1] * y[1][1] + lambda[2] * y[1][2]) || (-Primal_cplex.getObjValue() > lambda[1] * y[2][1] + lambda[2] * y[2][2])) {
                Next_y[1] = Primal_cplex.getValue(Primal_x[0]);
                Next_y[2] = Primal_cplex.getValue(Primal_x[1]);
                Useful = 1;
            }
        }

        Prime_run = clock() - Prime_start;
        Prime_run = Prime_run / CLOCKS_PER_SEC;
        Prime_time -= Prime_run;
        Primal_cplex.clear();
        Primal_model.remove(Primal_Obj);
    }

    virtual ~Prime() {
        delete[] lambda;
        delete[] Next_y;
        for (int i = 0; i < 3; i++) {
            delete[] y[i];
        }
        delete[] y;
    }
};

vector <Prime*>Tree_of_Primes;

void Primal_Finder() {

    Prime* New_Prime = new Prime;
    Primal_Obj = IloMinimize(env, -(0.001 * Primal_x[0]) - (0.999 * Primal_x[1]));
    Primal_model.add(Primal_Obj);
    Primal_cplex.extract(Primal_model);
    Mixed_integer = Primal_cplex.isMIP();
    if (Mixed_integer == 0) {
        Global_LB = Negative_infinity;
        goto Primal_end;
    }
    Primal_cplex.setParam(IloCplex::Threads, 1);
    Primal_cplex.setParam(IloCplex::TiLim, T_Limit);
    Primal_cplex.setParam(IloCplex::EpGap, Cplex_Gap);
    Primal_cplex.setOut(env.getNullStream());
    Number_of_LPs++;
    Prime_start = clock();
    if (Primal_cplex.solve()) {
        if(Primal_cplex.getMIPRelativeGap() <= Cplex_Gap){
        New_Prime->y[1][1] = Primal_cplex.getValue(Primal_x[0]);
        New_Prime->y[1][2] = Primal_cplex.getValue(Primal_x[1]);
        if (Primal_cplex.getValue(Primal_x[0]) * Primal_cplex.getValue(Primal_x[1]) > Global_LB) {
            for (int i = 0; i < N_Variables; i++) {
                Best_Solution[i] = Primal_cplex.getValue(Primal_x[i]);
            }
            Global_LB = Best_Solution[0] * Best_Solution[1];
            Primal_Solution = Global_LB;
        }
        if (Primal_Cut_Add == 1) {
            lp_model1.add(0.001 * Obj1 + 0.999 * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
            lp_model2.add(0.001 * Obj1 + 0.999 * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
            Zl_model.add(0.001 * Obj1 + 0.999 * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
            Check_model.add(0.001 * Obj1 + 0.999 * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
        }
    }
    } else {
        cout << "Infeasible, or could not solve in the time limit" << endl;
        Skip = 1;
    }
    Prime_run = clock() - Prime_start;
    Prime_run = Prime_run / CLOCKS_PER_SEC;
    if(Prime_run >= Primal_time){
        Prime_time = 0;
        bandb_time = T_Limit- Prime_run;
        if(bandb_time<0){
            bandb_time=0;
        }
    }else{
        bandb_time = T_Limit- Primal_time;
    Prime_time -= Prime_run;
    if (Prime_time < 0) {
        Prime_time = 0;
    }
    }
    Primal_cplex.clear();
    Primal_model.remove(Primal_Obj);
    Primal_Obj = IloMinimize(env, -(0.999 * Primal_x[0]) - (0.001 * Primal_x[1]));
    Primal_model.add(Primal_Obj);
    Primal_cplex.extract(Primal_model);
    Primal_cplex.setParam(IloCplex::Threads, 1);
    Primal_cplex.setParam(IloCplex::TiLim, Prime_time);
    Primal_cplex.setParam(IloCplex::EpGap, Cplex_Gap);
    Primal_cplex.setOut(env.getNullStream());
    Number_of_LPs++;
    Prime_start = clock();
    if (Primal_cplex.solve()) {
        if(Primal_cplex.getMIPRelativeGap() <= Cplex_Gap){
        New_Prime->y[2][1] = Primal_cplex.getValue(Primal_x[0]);
        New_Prime->y[2][2] = Primal_cplex.getValue(Primal_x[1]);
        if (Primal_cplex.getValue(Primal_x[0]) * Primal_cplex.getValue(Primal_x[1]) > Global_LB) {
            for (int i = 0; i < N_Variables; i++) {
                Best_Solution[i] = Primal_cplex.getValue(Primal_x[i]);
            }
            Global_LB = Best_Solution[0] * Best_Solution[1];
            Primal_Solution = Global_LB;
        }
        if (Primal_Cut_Add == 1) {
            lp_model1.add(0.999 * Obj1 + 0.001 * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
            lp_model2.add(0.999 * Obj1 + 0.001 * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
            Zl_model.add(0.999 * Obj1 + 0.001 * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
            Check_model.add(0.999 * Obj1 + 0.001 * Obj2 <= -Primal_cplex.getObjValue() + epsilon);
        }
    }
    }
    Prime_run = clock() - Prime_start;
    Prime_run = Prime_run / CLOCKS_PER_SEC;
    Prime_time -= Prime_run;
    if (Prime_time < 0) {
        Prime_time = 0;
    }
    Primal_cplex.clear();
    Primal_model.remove(Primal_Obj);
    New_Prime-> Explore_Prime();
    if (New_Prime->Useful == 1) {
        Tree_of_Primes.push_back(New_Prime);
    }

    while (Prime_time > 0 && Tree_of_Primes.size() > 0) {

        Prime* New_Prime_1 = new Prime;
        New_Prime_1->Initialize_Prime(Tree_of_Primes.front(), 1);
        Prime* New_Prime_2 = new Prime;
        New_Prime_2->Initialize_Prime(Tree_of_Primes.front(), 2);

        Tree_of_Primes.front()->~Prime();
        Tree_of_Primes.erase(Tree_of_Primes.begin());

        New_Prime_1->Explore_Prime();
        if (New_Prime_1->Useful == 1) {
            Tree_of_Primes.push_back(New_Prime_1);
        }
        if (Prime_time < 0) {
            Prime_time = 0;
        }
        New_Prime_2->Explore_Prime();
        if (New_Prime_2->Useful == 1) {
            Tree_of_Primes.push_back(New_Prime_2);
        }
    }
    while (Tree_of_Primes.size() > 0) {
        Tree_of_Primes.front()->~Prime();
        Tree_of_Primes.erase(Tree_of_Primes.begin());
    }
Primal_end:
    Primal_cplex.clear();
    Primal_model.end();
    Primal_Constraints.clear();
    Primal_Constraints.end();
    Primal_Obj.end();
    Primal_x.clear();
    Primal_x.end();
}

void Upper_Bound_Finder() {
    lp_cplex1.extract(lp_model1);
    lp_cplex2.extract(lp_model2);
    lp_cplex1.setParam(IloCplex::Threads, 1);
    lp_cplex1.setParam(IloCplex::TiLim, bandb_time);
    lp_cplex1.setParam(IloCplex::EpOpt, Cplex_Gap);
    lp_cplex2.setParam(IloCplex::Threads, 1);
    lp_cplex2.setParam(IloCplex::TiLim, bandb_time);
    lp_cplex2.setParam(IloCplex::EpOpt, Cplex_Gap);

    bandb_start = clock();

    Number_of_LPs += 2;
    if (lp_cplex1.solve() && lp_cplex2.solve()) {
        zu1 = lp_cplex1.getObjValue();
        zu2 = lp_cplex2.getObjValue();
    }
    bandb_run = clock() - bandb_start;
    bandb_run = bandb_run / CLOCKS_PER_SEC;
    bandb_time -= bandb_run;
    if (bandb_time < 0) {
        bandb_time = 0;
    }
    lp_cplex1.clear();
    lp_cplex2.clear();
}

void Intersection_Finder() {
    Zl_model.remove(Intersection_Constraint); 
    Intersection_Constraint.clear();
    Math.clear();
    Math = ((zu2 * Obj1) - (zu1 * Obj2));
    Intersection_Constraint.add(Math <= epsilon);
    Intersection_Constraint.add(Math >= -epsilon); 
    Math.clear();
    Zl_model.add(Intersection_Constraint);

    Zl_cplex.extract(Zl_model);

    Zl_cplex.setParam(IloCplex::Threads, 1);
    Zl_cplex.setParam(IloCplex::TiLim, bandb_time);
    Zl_cplex.setParam(IloCplex::EpOpt, Cplex_Gap);
    Number_of_LPs++;
    bandb_start = clock();
    if (Zl_cplex.solve()) {
        ZI[1] = Zl_cplex.getValue(Obj1);
        ZI[2] = Zl_cplex.getValue(Obj2);
        if (ZI[1] * ZI[2] > zl1 * zl2) {
            zl1 = ZI[1];
            zl2 = ZI[2];
            for (int i = 0; i < N_Variables; i++) {
                Solution[i] = Zl_cplex.getValue(var_x[i]);
            }
        }
    }
    bandb_run = clock() - bandb_start;
    bandb_run = bandb_run / CLOCKS_PER_SEC;
    bandb_time -= bandb_run;
    if (bandb_time < 0) {
        bandb_time = 0;
    }

    Zl_cplex.clear();

}

void Cutting_Plane_Adding() {
    Cutting_Plane_Value = 0;
    Cutting_Plane_Value = (ZI[1] / zu1) + (ZI[2] / zu2); 
    Cutting_Plane.clear();
    Cutting_Plane.add(-(Obj1 / zu1) - (Obj2 / zu2) <= -Cutting_Plane_Value - cut_epsilon); 
    lp_model1.add(Cutting_Plane);
    lp_model2.add(Cutting_Plane);
    Upper_Bound_Finder();
    lp_model1.remove(Cutting_Plane); 
    lp_model2.remove(Cutting_Plane);
    lp_model1.remove(Cutting_Plane_Obj);
    lp_model2.remove(Cutting_Plane_Obj);
    Zl_model.remove(Cutting_Plane_Obj);
    Check_model.remove(Cutting_Plane_Obj);
    Cutting_Plane_Obj.clear();
    Cutting_Plane_Obj.add(Obj1 <= zu1); 
    Cutting_Plane_Obj.add(Obj2 <= zu2);
    lp_model1.add(Cutting_Plane_Obj);
    lp_model2.add(Cutting_Plane_Obj);
    Zl_model.add(Cutting_Plane_Obj);
    Check_model.add(Cutting_Plane_Obj);
}

void Check_Feasible_Region() {
    Check_Value = 0;
    Check_Obj = IloMaximize(env, (Obj1 / zu1) + (Obj2 / zu2));
    Check_model.add(Check_Obj);
    Check_cplex.extract(Check_model);
    Check_cplex.setParam(IloCplex::Threads, 1);
    Check_cplex.setParam(IloCplex::TiLim, bandb_time);
    Check_cplex.setParam(IloCplex::EpOpt, Cplex_Gap);
    Number_of_LPs++;
    bandb_start = clock();
    if (Check_cplex.solve()) {
        Check_Value = Check_cplex.getObjValue();
    }
    bandb_run = clock() - bandb_start;
    bandb_run = bandb_run / CLOCKS_PER_SEC;
    bandb_time -= bandb_run;
    if (bandb_time < 0) {
        bandb_time = 0;
    }
    Check_model.remove(Check_Obj);

    Check_cplex.clear();

}

void PMP_A() {
    zlast1 = Positive_infinity;
    zlast2 = Positive_infinity;
    Search = 0;
    Optimal_checker = 0;
    Infeasibility = 1;
    zl1 = 0;
    zl2 = 0;
    lp_cplex1.extract(lp_model1);
    lp_cplex2.extract(lp_model2);
    lp_cplex1.setParam(IloCplex::Threads, 1);
    lp_cplex1.setParam(IloCplex::TiLim, bandb_time);
    lp_cplex1.setParam(IloCplex::EpOpt, Cplex_Gap);
    lp_cplex2.setParam(IloCplex::Threads, 1);
    lp_cplex2.setParam(IloCplex::TiLim, bandb_time);
    lp_cplex2.setParam(IloCplex::EpOpt, Cplex_Gap);
    bandb_start = clock();
    Number_of_LPs += 2;
    if (lp_cplex1.solve() && lp_cplex2.solve()) {
        zu1 = lp_cplex1.getObjValue();
        zu2 = lp_cplex2.getObjValue();
        Infeasibility = 0;
    }
    bandb_run = clock() - bandb_start;
    bandb_run = bandb_run / CLOCKS_PER_SEC;
    bandb_time -= bandb_run;
    if (bandb_time < 0) {
        bandb_time = 0;
    }
    lp_cplex1.clear();
    lp_cplex2.clear();
    if (Infeasibility == 0) {
        while (bandb_time > 0 && Search == 0) {
            vzu = zu1*zu2;
            vy = zl1*zl2;
            if (((vzu - vy) / (vzu + denominator)) <= Rel_Optimal_Tol || (zu1 >= zlast1 - Constraint_Modifier(zlast1) && zu2 >= zlast2 - Constraint_Modifier(zlast2)) || vzu - vy <= Abs_Optimal_Tol) {
                Search = 1;
            } else {
                zlast1 = zu1;
                zlast2 = zu2;
                Intersection_Finder();
                vy = zl1*zl2;
                Check_Feasible_Region();
                if (Check_Value + Constraint_Modifier(Check_Value)> (zl1 / (zu1 + denominator))+(zl2 / (zu2 + denominator)) && ((vzu - vy) / (vzu + denominator)) > Rel_Optimal_Tol) {
                    Cutting_Plane_Adding();
                } else {
                    Search = 1;
                }
            }

        }
    }
    Optimal_checker = Search;
    lp_model1.remove(Cutting_Plane_Obj);
    lp_model2.remove(Cutting_Plane_Obj);
    Zl_model.remove(Cutting_Plane_Obj);
    Check_model.remove(Cutting_Plane_Obj);
}

class Node {
public:

    int Node_Index;
    double score;
    int Next_Cut_Index;
    double Next_Cut_RHS;
    bool Next_Cut_Sign;
    bool Node_Optimality;
    bool Feasibility_Identifier;
    double Fr;
    vector <int> Var_Index;
    vector <bool> Constraint_Sign;
    vector <double> Constraint_RHS;
    double UB;
    bool Integrality;

    Node() {
        Integrality = 1;
        score = 0;
        Node_Optimality = 0;
    }

    void Reinitializing_The_Node(Node* Parent, bool Sign) {
        bandb_start = clock();
        Next_Cut_Sign = Sign;
        Next_Cut_Index = Parent ->Next_Cut_Index;
        Node_Index = Number_of_Explored_Nodes;
        Number_of_Explored_Nodes++;
        Node_Index_Added = 0;
        for (int i = 0; i < Parent->Var_Index.size(); i++) {
            Var_Index.push_back(Parent -> Var_Index.at(i));
            Constraint_Sign.push_back(Parent -> Constraint_Sign.at(i));
            if (Next_Cut_Index == Parent -> Var_Index.at(i) && Sign == Parent -> Constraint_Sign.at(i)) {
                if (Sign == 0) {
                    Constraint_RHS.push_back(std::min(Parent ->Next_Cut_RHS, Parent -> Constraint_RHS.at(i)));
                    Node_Index_Added = 1;
                }
                if (Sign == 1) {
                    Constraint_RHS.push_back(std::max(Parent ->Next_Cut_RHS + 1, Parent -> Constraint_RHS.at(i)));
                    Node_Index_Added = 1;
                }
            } else {
                Constraint_RHS.push_back(Parent -> Constraint_RHS.at(i));
            }
        }
        if (Node_Index_Added == 0) {
            if (Sign == 0) {
                Var_Index.push_back(Parent->Next_Cut_Index);
                Constraint_Sign.push_back(Sign);
                Constraint_RHS.push_back(Parent ->Next_Cut_RHS);
            }
            if (Sign == 1) {
                Var_Index.push_back(Parent ->Next_Cut_Index);
                Constraint_Sign.push_back(Sign);
                Constraint_RHS.push_back(Parent ->Next_Cut_RHS + 1);
            }
        }

        UB = Parent->UB;
        Fr = Parent->Fr;
bandb_run = clock() - bandb_start;
    bandb_run = bandb_run / CLOCKS_PER_SEC;
    bandb_time -= bandb_run;
    if (bandb_time < 0) {
        bandb_time = 0;
    }
    }

    void Explore_The_Node() {
        for (int k = 0; k < Var_Index.size(); k++) {
            RHS = Constraint_RHS.at(k);
            Index = Var_Index.at(k);
            SSign = Constraint_Sign.at(k);
            if (SSign == 0) {
                BandB_Constraints.add(var_x[Index] <= RHS);
            }
            if (SSign == 1) {
                BandB_Constraints.add(var_x[Index] >= RHS);
            }
        }
        lp_model1.add(BandB_Constraints);
        lp_model2.add(BandB_Constraints);
        Zl_model.add(BandB_Constraints);
        Check_model.add(BandB_Constraints);
        PMP_A();
        Node_Optimality = Optimal_checker;
        UB_temp = UB;
        Feasibility_Identifier = Infeasibility;
        if (Feasibility_Identifier == 0) {
            UB = Solution[0] * Solution[1];
            if (Node_Optimality == 1) {

                if (Branching == 1) {
                    bandb_start = clock();
                    Fr_index = 0;
                    for (int i = 0; i < N_Variables; i++) {
                        if (Type[i] != 2) {
                            Fracpart = modf(Solution[i], &Intpart);
                            if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                Integrality = 0;
                                Fr_index++;
                            }
                        }
                    }
                    if (Integrality == 0) {
                        Random_index = rand() % Fr_index + 1;
                        Fr_index = 0;
                        for (int i = 0; i < N_Variables; i++) {
                            if (Type[i] != 2) {
                                Fracpart = modf(Solution[i], &Intpart); 
                                if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                    Fr_index++;
                                    if (Fr_index == Random_index) {
                                        Next_Cut_Index = i;
                                        Next_Cut_RHS = Intpart;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    bandb_run = clock() - bandb_start;
    bandb_run = bandb_run / CLOCKS_PER_SEC;
    bandb_time -= bandb_run;
    if (bandb_time < 0) {
        bandb_time = 0;
    }
                }
                else if (Branching == 2) {
                    si = 0;
                    if (Next_Cut_Sign == 0 && n_minus[Next_Cut_Index] > threshold) {
                        if ((UB_temp - UB) / Fr >= 0) {
                            p_minus[Next_Cut_Index] += ((UB_temp - UB) / Fr);
                        } else if ((UB_temp - UB) / Fr < 0) {
                            p_minus[Next_Cut_Index] -= ((UB_temp - UB) / Fr);
                        }
                        n_minus[Next_Cut_Index]++;
                    } else if (Next_Cut_Sign == 0 && n_minus[Next_Cut_Index] == threshold) {
                        n_minus[Next_Cut_Index]++;
                    } else if (Next_Cut_Sign == 1 && n_plus[Next_Cut_Index] > threshold) {
                        if ((UB_temp - UB) / (1 - Fr) >= 0) {
                            p_plus[Next_Cut_Index] += ((UB_temp - UB) / (1 - Fr));
                        } else if ((UB_temp - UB) / (1 - Fr) < 0) {
                            p_plus[Next_Cut_Index] -= ((UB_temp - UB) / (1 - Fr));
                        }
                        n_plus[Next_Cut_Index]++;
                    } else if (Next_Cut_Sign == 1 && n_plus[Next_Cut_Index] == threshold) {
                        n_plus[Next_Cut_Index]++;
                    }
                    for (int i = 0; i < N_Variables; i++) {
                        if (Type[i] != 2) {
                            Fracpart = modf(Solution[i], &Intpart); 
                            if (Fracpart > Constraint_Modifier(Solution[i]) && Fracpart < 1 - Constraint_Modifier(Solution[i])) {
                                Integrality = 0;
                                if (n_plus[i] == threshold) {
                                    D_plus[i] = (1 - Fracpart) * p_plus[i] / (n_plus[i]);
                                } else if (n_plus[i] > threshold) {
                                    D_plus[i] = (1 - Fracpart) * p_plus[i] / (n_plus[i] - 1);
                                } else if (n_plus[i] < threshold) {
                                    Strong.add(var_x[i] >= Intpart + 1);
                                    lp_model1.add(Strong);
                                    lp_model2.add(Strong);
                                    Zl_model.add(Strong);
                                    Check_model.add(Strong);
                                    PMP_A();
                                    lp_model1.remove(Strong);
                                    lp_model2.remove(Strong);
                                    Zl_model.remove(Strong);
                                    Check_model.remove(Strong);
                                    Strong.clear();
                                    if (Infeasibility == 0) {
                                        if ((UB - (Solution[0] * Solution[1])) / (1 - Fracpart) >= 0) {
                                            p_plus[i] += ((UB - (Solution[0] * Solution[1])) / (1 - Fracpart));
                                        } else if ((UB - (Solution[0] * Solution[1])) / (1 - Fracpart) < 0) {
                                            p_plus[i] -= ((UB - (Solution[0] * Solution[1])) / (1 - Fracpart));
                                        }
                                        n_plus[i]++;
                                        D_plus[i] = ((1 - Fracpart) * p_plus[i] / n_plus[i]);
                                    }
                                }
                                if (n_minus[i] == threshold) {
                                    D_minus[i] = Fracpart * (p_minus[i] / (n_minus[i] - 1));
                                } else if (n_minus[i] > threshold) {
                                    D_minus[i] = Fracpart * (p_minus[i] / (n_minus[i] - 1));
                                } else if (n_minus[i] < threshold) {
                                    Strong.add(var_x[i] <= Intpart);
                                    lp_model1.add(Strong);
                                    lp_model2.add(Strong);
                                    Zl_model.add(Strong);
                                    Check_model.add(Strong);
                                    PMP_A();
                                    lp_model1.remove(Strong);
                                    lp_model2.remove(Strong);
                                    Zl_model.remove(Strong);
                                    Check_model.remove(Strong);
                                    Strong.clear();
                                    if (Infeasibility == 0) {
                                        if ((UB - (Solution[0] * Solution[1])) / Fracpart >= 0) {
                                            p_minus[i] += ((UB - (Solution[0] * Solution[1])) / Fracpart);
                                        } else if ((UB - (Solution[0] * Solution[1])) / Fracpart < 0) {
                                            p_minus[i] -= ((UB - (Solution[0] * Solution[1])) / Fracpart);
                                        }
                                        n_minus[i]++;
                                        D_minus[i] = Fracpart * (p_minus[i] / n_minus[i]);
                                    }
                                }
                                if (Noding == 5) {
                                    score -= std::min(D_minus[i], D_plus[i]);
                                }
                                si_temp = Strong_mu * (std::min(D_minus[i], D_plus[i])) + (1 - Strong_mu)*(std::max(D_minus[i], D_plus[i]));
                                if (si_temp > si) {
                                    si = si_temp;
                                    Next_Cut_Index = i;
                                    Next_Cut_RHS = Intpart;
                                    Fr = Fracpart;

                                }
                            }
                        }
                    }
                    if (Noding == 4 && Integrality == 0) {
                        b_plus = UB - D_plus[Next_Cut_Index];
                        b_minus = UB - D_minus[Next_Cut_Index];
                        score = std::max(b_plus, b_minus);
                    } else if (Noding == 5 && Integrality == 0) {
                        score += UB;
                    }
                }
                else if (Branching == 3) {
                    bandb_start = clock();
                    si = 0;
                    for (int i = 0; i < N_Variables; i++) {
                        if (Type[i] != 2) {
                            Fracpart = modf(Solution[i], &Intpart); 
                            if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                Integrality = 0;
                                if (std::min(Fracpart, 1 - Fracpart) > si) {
                                    si = std::min(Fracpart, 1 - Fracpart);
                                    Next_Cut_Index = i;
                                    Next_Cut_RHS = Intpart;
                                }
                            }
                        }
                        if(si >= (0.5-epsilon) && si <= (0.5 + epsilon)){
                            break;
                        }
                    }
                    bandb_run = clock() - bandb_start;
    bandb_run = bandb_run / CLOCKS_PER_SEC;
    bandb_time -= bandb_run;
    if (bandb_time < 0) {
        bandb_time = 0;
    }
                }                    
                else if (Branching == 4) {
                    bandb_start = clock();
                    si = -1;
                    if (Psuedocost_counter != 0) {
                        if (Next_Cut_Sign == 0) {
                            if ((UB_temp - UB) / Fr >= 0) {
                                p_minus[Next_Cut_Index] += ((UB_temp - UB) / Fr);
                            } else if ((UB_temp - UB) / Fr < 0) {
                                p_minus[Next_Cut_Index] -= ((UB_temp - UB) / Fr);
                            }
                            n_minus[Next_Cut_Index]++;

                        } else if (Next_Cut_Sign == 1) {
                            if ((UB_temp - UB) / (1 - Fr) >= 0) {
                                p_plus[Next_Cut_Index] += ((UB_temp - UB) / (1 - Fr));
                            } else if ((UB_temp - UB) / (1 - Fr) < 0) {
                                p_plus[Next_Cut_Index] -= ((UB_temp - UB) / (1 - Fr));
                            }
                            n_plus[Next_Cut_Index]++;
                        }
                    }
                    if (Psuedocost_counter > 10) {
                        Fr_index = 0;
                        for (int i = 0; i < N_Variables; i++) {
                            if (Type[i] != 2) {
                                Fracpart = modf(Solution[i], &Intpart); 
                                if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                    Fr_index++;
                                    Integrality = 0;
                                    if (n_minus[i] > 0) {
                                        D_minus[i] = Fracpart * (p_minus[i] / n_minus[i]);
                                    }
                                    if (n_plus[i] > 0) {
                                        D_plus[i] = ((1 - Fracpart) * p_plus[i] / n_plus[i]);
                                    }
                                    if (Noding == 5) {
                                        score -= std::min(D_minus[i], D_plus[i]);
                                    }
                                    si_temp = Strong_mu * (std::min(D_minus[i], D_plus[i])) + (1 - Strong_mu)*(std::max(D_minus[i], D_plus[i]));
                                    if (si_temp > si) {
                                        si = si_temp;
                                        Next_Cut_Index = i;
                                        Next_Cut_RHS = Intpart;
                                        Fr = Fracpart;
                                    }
                                }
                            }
                        }

                        if (si <= epsilon && Integrality == 0) {
                            Random_index = rand() % Fr_index + 1;
                            Fr_index = 0;
                            for (int i = 0; i < N_Variables; i++) {
                                if (Type[i] != 2) {
                                    Fracpart = modf(Solution[i], &Intpart); 
                                    if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                        Fr_index++;
                                        if (Fr_index == Random_index) {
                                            Next_Cut_Index = i;
                                            Next_Cut_RHS = Intpart;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        Fr_index = 0;
                        for (int i = 0; i < N_Variables; i++) {
                            if (Type[i] != 2) {
                                Fracpart = modf(Solution[i], &Intpart); 
                                if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                    Integrality = 0;
                                    Fr_index++;
                                    if (n_minus[i] > 0) {
                                        D_minus[i] = Fracpart * (p_minus[i] / n_minus[i]);
                                    }
                                    if (n_plus[i] > 0) {
                                        D_plus[i] = ((1 - Fracpart) * p_plus[i] / n_plus[i]);
                                    }
                                    if (Noding == 5) {
                                        score -= std::min(D_minus[i], D_plus[i]);
                                    }
                                }
                            }
                        }

                        if (Integrality == 0) {
                            Random_index = rand() % Fr_index + 1;
                            Fr_index = 0;
                            for (int i = 0; i < N_Variables; i++) {
                                if (Type[i] != 2) {
                                    Fracpart = modf(Solution[i], &Intpart); 
                                    if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                        Fr_index++;
                                        if (Fr_index == Random_index) {
                                            Next_Cut_Index = i;
                                            Next_Cut_RHS = Intpart;
                                            break;
                                        }
                                    }
                                }
                            }
                        }

                    }

                    Psuedocost_counter++;
                    if (Noding == 4 && Integrality == 0) {
                        b_plus = UB - D_plus[Next_Cut_Index];
                        b_minus = UB - D_minus[Next_Cut_Index];
                        score = std::max(b_plus, b_minus);
                    } else if (Noding == 5 && Integrality == 0) {
                        score += UB;
                    }
                bandb_run = clock() - bandb_start;
    bandb_run = bandb_run / CLOCKS_PER_SEC;
    bandb_time -= bandb_run;
    if (bandb_time < 0) {
        bandb_time = 0;
    }
                }                    
                else if (Branching == 5) {
                    bandb_start = clock();
                    si = -1;
                    if (Psuedocost_counter != 0) {
                        if (Next_Cut_Sign == 0) {
                            if ((UB_temp - UB) / Fr >= 0) {
                                p_minus[Next_Cut_Index] += ((UB_temp - UB) / Fr);
                            } else if ((UB_temp - UB) / Fr < 0) {
                                p_minus[Next_Cut_Index] -= ((UB_temp - UB) / Fr);
                            }
                            n_minus[Next_Cut_Index]++;

                        } else if (Next_Cut_Sign == 1) {
                            if ((UB_temp - UB) / (1 - Fr) >= 0) {
                                p_plus[Next_Cut_Index] += ((UB_temp - UB) / (1 - Fr));
                            } else if ((UB_temp - UB) / (1 - Fr) < 0) {
                                p_plus[Next_Cut_Index] -= ((UB_temp - UB) / (1 - Fr));
                            }
                            n_plus[Next_Cut_Index]++;

                        }
                    }
                    if (Psuedocost_counter > 10) {
                        for (int i = 0; i < N_Variables; i++) {
                            if (Type[i] != 2) {
                                Fracpart = modf(Solution[i], &Intpart); 
                                if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                    Integrality = 0;
                                    if (n_minus[i] > 0) {
                                        D_minus[i] = Fracpart * (p_minus[i] / n_minus[i]);
                                    }
                                    if (n_plus[i] > 0) {
                                        D_plus[i] = ((1 - Fracpart) * p_plus[i] / n_plus[i]);
                                    }
                                    if (Noding == 5) {
                                        score -= std::min(D_minus[i], D_plus[i]);
                                    }
                                    si_temp = Strong_mu * (std::min(D_minus[i], D_plus[i])) + (1 - Strong_mu)*(std::max(D_minus[i], D_plus[i]));
                                    if (si_temp > si) {
                                        si = si_temp;
                                        Next_Cut_Index = i;
                                        Next_Cut_RHS = Intpart;
                                        Fr = Fracpart;
                                    }
                                }
                            }
                        }

                        if (si <= epsilon && Integrality == 0) {
                            si = 0;
                            for (int i = 0; i < N_Variables; i++) {
                                if (Type[i] != 2) {
                                    Fracpart = modf(Solution[i], &Intpart); 
                                    if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                        if (std::min(Fracpart, 1 - Fracpart) > si) {
                                            si = std::min(Fracpart, 1 - Fracpart);
                                            Next_Cut_Index = i;
                                            Next_Cut_RHS = Intpart;
                                            Fr = Fracpart;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        for (int i = 0; i < N_Variables; i++) {
                            if (Type[i] != 2) {
                                Fracpart = modf(Solution[i], &Intpart); 
                                if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                                    Integrality = 0;
                                    if (n_minus[i] > 0) {
                                        D_minus[i] = Fracpart * (p_minus[i] / n_minus[i]);
                                    }
                                    if (n_plus[i] > 0) {
                                        D_plus[i] = ((1 - Fracpart) * p_plus[i] / n_plus[i]);
                                    }
                                    if (Noding == 5) {
                                        score -= std::min(D_minus[i], D_plus[i]);
                                    }
                                    if (std::min(Fracpart, 1 - Fracpart) > si) {
                                        si = std::min(Fracpart, 1 - Fracpart);
                                        Next_Cut_Index = i;
                                        Next_Cut_RHS = Intpart;
                                        Fr = Fracpart;
                                    }
                                }
                            }
                        }
                    }

                    Psuedocost_counter++;
                    if (Noding == 4 && Integrality == 0) {
                        b_plus = UB - D_plus[Next_Cut_Index];
                        b_minus = UB - D_minus[Next_Cut_Index];
                        score = std::max(b_plus, b_minus);
                    } else if (Noding == 5 && Integrality == 0) {
                        score += UB;
                    }
                bandb_run = clock() - bandb_start;
    bandb_run = bandb_run / CLOCKS_PER_SEC;
    bandb_time -= bandb_run;
    if (bandb_time < 0) {
        bandb_time = 0;
    }
                }

            }
        } else {
            Number_of_Infeasibles++;
        }
        lp_model1.remove(BandB_Constraints);
        lp_model2.remove(BandB_Constraints);
        Zl_model.remove(BandB_Constraints);
        Check_model.remove(BandB_Constraints);
        BandB_Constraints.clear();
    }

    virtual ~Node() {
        while (Var_Index.size() > 0) {
            Var_Index.erase(Var_Index.begin());
        }
        while (Constraint_Sign.size() > 0) {
            Constraint_Sign.erase(Constraint_Sign.begin());
        }
        while (Constraint_RHS.size() > 0) {
            Constraint_RHS.erase(Constraint_RHS.begin());
        }
    }
};

vector <Node*>Tree_of_Nodes;

void Add_the_new_node_to_the_tree(Node* New_Generated_Node) {

    It_is_Added = 0;
    if (Noding != 4 || Noding != 5) {
        for (int i = 0; i < Tree_of_Nodes.size(); i++) {
            if (New_Generated_Node->UB > Tree_of_Nodes.at(i)->UB + Constraint_Modifier(Tree_of_Nodes.at(i)->UB)) {
                Tree_of_Nodes.insert(Tree_of_Nodes.begin() + i, New_Generated_Node);
                It_is_Added = 1;
                break;
            }
        }
    } else {
        for (int i = 0; i < Tree_of_Nodes.size(); i++) {
            if (New_Generated_Node->score > Tree_of_Nodes.at(i)->score + epsilon) {
                Tree_of_Nodes.insert(Tree_of_Nodes.begin() + i, New_Generated_Node);
                It_is_Added = 1;
                break;
            }
        }
    }
    if (It_is_Added == 0) {
        Tree_of_Nodes.push_back(New_Generated_Node);
    }

}

void Create_The_Node_ZERO() {
    
    Node* New_Node = new Node;
    New_Node->Node_Index = 0;
    New_Node->Next_Cut_Sign = 0;
    New_Node->Next_Cut_Index = 1;
    New_Node->UB = Positive_infinity;
    New_Node-> Explore_The_Node();
    Number_of_Explored_Nodes++;
    Global_UB = New_Node->UB;
    if (New_Node->Feasibility_Identifier == 0 && New_Node->Node_Optimality == 1) {
        if (New_Node -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node->UB) {
            Tree_of_Nodes.push_back(New_Node);
        } else if (New_Node -> Integrality == 1 && Global_LB < New_Node->UB) {
            Global_LB = Global_UB;
            for (int j = 0; j < N_Variables; j++) {
                Best_Solution[j] = Solution[j];
                bestnode = New_Node->Node_Index;
            }
        }
    } else if (New_Node->Feasibility_Identifier == 0 && New_Node->Node_Optimality == 0) {
        for (int i = 0; i < N_Variables; i++) {
            if (Type[i] != 2) {
                Fracpart = modf(Solution[i], &Intpart);
                if (Fracpart >= Constraint_Modifier(Solution[i]) && Fracpart <= 1 - Constraint_Modifier(Solution[i])) {
                    New_Node->Integrality = 0;
                }
            }
        }
        if (New_Node -> Integrality == 1) {
            if (Global_UB > Global_LB) {
                Global_LB = Global_UB;
                for (int j = 0; j < N_Variables; j++) {
                    Best_Solution[j] = Solution[j];
                    bestnode = New_Node->Node_Index;
                }
            }
            cout << "Out-of-time" << "Best found solution is " << Global_LB << endl;
        } else if (Primal_search == 0) {
            cout << "out-of-time and nothing found" << endl;
            Skip = 1;
        }
    } else if (New_Node->Feasibility_Identifier == 1 && Primal_search == 0) {
        cout << "Infeasible" << endl;
        Skip = 1;
    }

    New_Node->~Node();
}

void Branch_and_Bound(int Noding) {
    while (bandb_time > 0 && Noding == 1 && Tree_of_Nodes.size() > 0 && Global_UB > Global_LB + Abs_Optimal_Tol && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol) {
        Node* New_Node_L = new Node;
        New_Node_L->Reinitializing_The_Node(Tree_of_Nodes.front(), 0);
        Node* New_Node_G = new Node;
        New_Node_G->Reinitializing_The_Node(Tree_of_Nodes.front(), 1);

        Tree_of_Nodes.front()->~Node();
        Tree_of_Nodes.erase(Tree_of_Nodes.begin());

        New_Node_L->Explore_The_Node();
        if (New_Node_L->Feasibility_Identifier == 0 && New_Node_L->Node_Optimality == 1) {
            if (New_Node_L -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                Add_the_new_node_to_the_tree(New_Node_L);
            } else if (New_Node_L -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                Global_LB = New_Node_L->UB;
                for (int j = 0; j < N_Variables; j++) {
                    Best_Solution[j] = Solution[j];
                    bestnode = New_Node_L->Node_Index;
                }
            } else {
                Pruned++;
            }
        }

        New_Node_G->Explore_The_Node();
        if (New_Node_G->Feasibility_Identifier == 0 && New_Node_G->Node_Optimality == 1) {
            if (New_Node_G -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                Add_the_new_node_to_the_tree(New_Node_G);
            } else if (New_Node_G -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                Global_LB = New_Node_G->UB;
                for (int j = 0; j < N_Variables; j++) {
                    Best_Solution[j] = Solution[j];
                    bestnode = New_Node_G->Node_Index;
                }
            } else {
                Pruned++;
            }
        }
        Global_UB = Tree_of_Nodes.front()->UB;
        if (Global_UB < Global_LB || Tree_of_Nodes.size() == 0) {
            Global_UB = Global_LB;
        }
    }
    while (bandb_time > 0 && Noding == 2 && Tree_of_Nodes.size() > 0 && Global_UB > Global_LB + Abs_Optimal_Tol && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol) {

        Node* New_Node_L = new Node;
        New_Node_L->Reinitializing_The_Node(Tree_of_Nodes.back(), 0);
        Node* New_Node_G = new Node;
        New_Node_G->Reinitializing_The_Node(Tree_of_Nodes.back(), 1);

        Tree_of_Nodes.back()->~Node();
        Tree_of_Nodes.erase(Tree_of_Nodes.end() - 1);

        New_Node_L->Explore_The_Node();
        if (New_Node_L->Feasibility_Identifier == 0 && New_Node_L->Node_Optimality == 1) {
            if (New_Node_L -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                Tree_of_Nodes.push_back(New_Node_L);

            } else if (New_Node_L -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                Global_LB = New_Node_L->UB;
                for (int j = 0; j < N_Variables; j++) {
                    Best_Solution[j] = Solution[j];
                    bestnode = New_Node_L->Node_Index;
                }
            } else {
                Pruned++;
            }
        }

        New_Node_G->Explore_The_Node();
        if (New_Node_G->Feasibility_Identifier == 0 && New_Node_G->Node_Optimality == 1) {
            if (New_Node_G -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                Tree_of_Nodes.push_back(New_Node_G);
            } else if (New_Node_G -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                Global_LB = New_Node_G->UB;
                for (int j = 0; j < N_Variables; j++) {
                    Best_Solution[j] = Solution[j];
                    bestnode = New_Node_G->Node_Index;
                }
            } else {
                Pruned++;
            }
        }

        Global_UB = 0;
        for (int i = 0; i < Tree_of_Nodes.size(); i++) {
            if (Global_UB < Tree_of_Nodes.at(i)->UB) {
                Global_UB = Tree_of_Nodes.at(i)->UB;
            }
        }
        if (Global_UB < Global_LB || Tree_of_Nodes.size() == 0) {
            Global_UB = Global_LB;
        }

    }
    while (bandb_time > 0 && Noding == 3 && Tree_of_Nodes.size() > 0 && Global_UB > Global_LB + Abs_Optimal_Tol && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol) {
        int Counter;
        double Global_UB_Temp;
        double Global_LB_Temp;
        bool checker;
#define GreedUB 0.05
        
        Noding = 1;
Start_UB:
        Counter = 0;
        Global_UB = 0;
        for (int i = 0; i < Tree_of_Nodes.size(); i++) {
            if (Global_UB < Tree_of_Nodes.at(i)->UB) {
                Global_UB = Tree_of_Nodes.at(i)->UB;
                Next_Branch = i;
            }
        }
        Global_UB_Temp = Global_UB;
        while (bandb_time > 0 && Noding == 1 && Tree_of_Nodes.size() > 0 && Global_UB > Global_LB + Abs_Optimal_Tol && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol) {
            Counter++;
            Node* New_Node_L = new Node;
            New_Node_L->Reinitializing_The_Node(Tree_of_Nodes.at(Next_Branch), 0);
            Node* New_Node_G = new Node;
            New_Node_G->Reinitializing_The_Node(Tree_of_Nodes.at(Next_Branch), 1);

            Tree_of_Nodes.at(Next_Branch)->~Node();
            Tree_of_Nodes.erase(Tree_of_Nodes.begin() + Next_Branch);

            New_Node_L->Explore_The_Node();
            if (New_Node_L->Feasibility_Identifier == 0 && New_Node_L->Node_Optimality == 1) {
                if (New_Node_L -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                    Tree_of_Nodes.push_back(New_Node_L);
                } else if (New_Node_L -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                    Global_LB = New_Node_L->UB;
                    for (int j = 0; j < N_Variables; j++) {
                        Best_Solution[j] = Solution[j];
                        bestnode = New_Node_L->Node_Index;
                    }
                } else {
                    Pruned++;
                }
            }

            New_Node_G->Explore_The_Node();
            if (New_Node_G->Feasibility_Identifier == 0 && New_Node_G->Node_Optimality == 1) {
                if (New_Node_G -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                    Tree_of_Nodes.push_back(New_Node_G);
                } else if (New_Node_G -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                    Global_LB = New_Node_G->UB;
                    for (int j = 0; j < N_Variables; j++) {
                        Best_Solution[j] = Solution[j];
                        bestnode = New_Node_G->Node_Index;
                    }
                } else {
                    Pruned++;
                }
            }

            Global_UB = 0;
            for (int i = 0; i < Tree_of_Nodes.size(); i++) {
                if (Global_UB < Tree_of_Nodes.at(i)->UB) {
                    Global_UB = Tree_of_Nodes.at(i)->UB;
                    Next_Branch = i;
                }
            }
            if (Global_UB < Global_LB || Tree_of_Nodes.size() == 0) {
                Global_UB = Global_LB;
            }
            if (Counter == std::min(4 * N_Variables, 1000)) {
                if ((Global_UB_Temp - Global_UB) / Global_UB_Temp < GreedUB) {
                    Noding = 2;
                    goto Start_LB;
                } else {
                    goto Start_UB;
                }
            }
        }
Start_LB:
        Counter = 0;
        Global_LB_Temp = Global_LB;
        while (bandb_time > 0 && Noding == 2 && Tree_of_Nodes.size() > 0 && Global_UB > Global_LB + Abs_Optimal_Tol && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol) {
            Counter++;
            checker = 0;
            Node* New_Node_L = new Node;
            New_Node_L->Reinitializing_The_Node(Tree_of_Nodes.back(), 0);
            Node* New_Node_G = new Node;
            New_Node_G->Reinitializing_The_Node(Tree_of_Nodes.back(), 1);

            Tree_of_Nodes.back()->~Node();
            Tree_of_Nodes.erase(Tree_of_Nodes.end() - 1);

            New_Node_L->Explore_The_Node();
            if (New_Node_L->Feasibility_Identifier == 0 && New_Node_L->Node_Optimality == 1) {
                if (New_Node_L -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                    Tree_of_Nodes.push_back(New_Node_L);

                } else if (New_Node_L -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                    checker = 1;
                    Global_LB = New_Node_L->UB;
                    for (int j = 0; j < N_Variables; j++) {
                        Best_Solution[j] = Solution[j];
                        bestnode = New_Node_L->Node_Index;
                    }
                } else {
                    Pruned++;
                }
            }

            New_Node_G->Explore_The_Node();
            if (New_Node_G->Feasibility_Identifier == 0 && New_Node_G->Node_Optimality == 1) {
                if (New_Node_G -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                    Tree_of_Nodes.push_back(New_Node_G);
                } else if (New_Node_G -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                    checker = 1;
                    Global_LB = New_Node_G->UB;
                    for (int j = 0; j < N_Variables; j++) {
                        Best_Solution[j] = Solution[j];
                        bestnode = New_Node_G->Node_Index;
                    }
                } else {
                    Pruned++;
                }
            }

            Global_UB = 0;
            for (int i = 0; i < Tree_of_Nodes.size(); i++) {
                if (Global_UB < Tree_of_Nodes.at(i)->UB) {
                    Global_UB = Tree_of_Nodes.at(i)->UB;
                }
            }
            if (Global_UB < Global_LB || Tree_of_Nodes.size() == 0) {
                Global_UB = Global_LB;
            }
            if (checker == 1 || Counter == std::min(3 * N_Variables, 1000)) {
                Noding = 1;
                goto Start_UB;
            }

        }
        if (Global_UB < Global_LB || Tree_of_Nodes.size() == 0) {
            Global_UB = Global_LB;
        }
    }
    while (bandb_time > 0 && (Noding == 4 || Noding == 5) && Tree_of_Nodes.size() > 0 && Global_UB > Global_LB + Abs_Optimal_Tol && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol) {

        Node* New_Node_L = new Node;
        New_Node_L->Reinitializing_The_Node(Tree_of_Nodes.front(), 0);
        Node* New_Node_G = new Node;
        New_Node_G->Reinitializing_The_Node(Tree_of_Nodes.front(), 1);

        Tree_of_Nodes.front()->~Node();
        Tree_of_Nodes.erase(Tree_of_Nodes.begin());

        New_Node_L->Explore_The_Node();
        if (New_Node_L->Feasibility_Identifier == 0 && New_Node_L->Node_Optimality == 1) {
            if (New_Node_L -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                Add_the_new_node_to_the_tree(New_Node_L);
            } else if (New_Node_L -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_L->UB) {
                Global_LB = New_Node_L->UB;
                for (int j = 0; j < N_Variables; j++) {
                    Best_Solution[j] = Solution[j];
                    bestnode = New_Node_L->Node_Index;
                }
            } else {
                Pruned++;
            }
        }

        New_Node_G->Explore_The_Node();
        if (New_Node_G->Feasibility_Identifier == 0 && New_Node_G->Node_Optimality == 1) {
            if (New_Node_G -> Integrality == 0 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                Add_the_new_node_to_the_tree(New_Node_G);
            } else if (New_Node_G -> Integrality == 1 && Abs_Optimal_Tol + Global_LB < New_Node_G->UB) {
                Global_LB = New_Node_G->UB;
                for (int j = 0; j < N_Variables; j++) {
                    Best_Solution[j] = Solution[j];
                    bestnode = New_Node_G->Node_Index;
                }
            } else {
                Pruned++;
            }
        }

        Global_UB = 0;
        for (int i = 0; i < Tree_of_Nodes.size(); i++) {
            if (Global_UB < Tree_of_Nodes.at(i)->UB) {
                Global_UB = Tree_of_Nodes.at(i)->UB;
            }
        }
        if (Global_UB < Global_LB || Tree_of_Nodes.size() == 0) {
            Global_UB = Global_LB;
        }
    }

    if (bandb_time > 0 || Global_UB < Global_LB + Abs_Optimal_Tol || (Global_UB - Global_LB) / (Global_UB + denominator) < Rel_Optimal_Tol) {
        Global_UB = Global_LB;
        Optimality = 1;
    }
}

int main(int argc, char *argv[]) {
    gettimeofday(&startTime, NULL);
    IP_file_name = argv[1];
    LP_file_name = argv[2];
    Branching = atoi(argv[3]);
    Noding = atoi(argv[4]);
    Primal_search = atoi(argv[5]);
    Primal_Cut_Add = atoi(argv[6]);

    bandb_time = T_Limit;
    Getting_Integers();
    lp_cplex1.setOut(env.getNullStream());
    lp_cplex2.setOut(env.getNullStream());
    Zl_cplex.setOut(env.getNullStream());
    Primal_cplex.setOut(env.getNullStream());
    Check_cplex.setOut(env.getNullStream());
    if (Primal_search == 1) {
        Prime_time = (N_Variables - 2) / 10;
        Primal_time = (N_Variables - 2) / 10;
        Primal_Finder();
    } else {
        Global_LB = Negative_infinity;
    }
    clock_start_time = clock();

    if (Skip == 0) {
        Create_The_Node_ZERO();
        Branch_and_Bound(Noding);
    }

    clock_Run_time = (clock() - clock_start_time);
    Open_Nodes = Tree_of_Nodes.size();
    gettimeofday(&endTime, NULL);
    if (Skip == 0) {
        Writing_The_Output_File();
    }
    return 0;
}