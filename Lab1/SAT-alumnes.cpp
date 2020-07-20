#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <stack>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

typedef vector<int> clause;

uint numVars;
uint numClauses;
vector<clause> clauses;
vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

struct occursLiteral {
    uint literal;
    vector<uint> occursPos;
    vector<uint> occursNeg;
    
};

vector<occursLiteral> occursList;
vector<occursLiteral> occursListOrderedBySize;

struct occursAbsLiteral {
    uint literal;
    vector<uint> occurs;
    
};

vector<occursAbsLiteral> absOccursList;
vector<occursAbsLiteral> absOccursListOrderedBySize;
    
struct clausesGroup {   
    vector<clause> clauses;
    vector<bool> litsIn;   
    
};

vector<clausesGroup> clausesGroups;

vector<uint> conflictLits;
int decisionCounter;
int conflictDecisions;

void printStats() {
    cout << "c " << decisionCounter << " decisions" << endl;
    
    
}


void printClause(const clause& c) {
    cout << "(" << c[0] << ", " << c[1] << ", " << c[2] << ")";
        
    
}


bool sortingClauses(const vector<int>& a, const vector<int>& b) {
    for (uint i = 0; i < a.size(); ++i) {
            if (a[i] < b[i]) return true;
            else if (a[i] > b[i]) return false;      
    }
    return false;
    
}


bool sortByAbsOccurs(const occursAbsLiteral& a, const occursAbsLiteral& b) {
    if (b.occurs.size() < a.occurs.size()) return true;
    else return false;
    
}


bool sortByOccurs(const occursLiteral& a, const occursLiteral& b) {
    int aMaxSize = max(a.occursPos.size(), a.occursNeg.size());
    int bMaxSize = max(b.occursPos.size(), b.occursNeg.size());
    if (bMaxSize < aMaxSize) return true;
    else return false;
    
}


vector<int> invertClause(const vector<int>& c) {
    vector<int> ret;
    for (uint i = 0; i < c.size(); ++i) {
            ret.push_back(-c[i]);
    }
    return ret;
}


bool tautologyTest(const clause& c) {
    bool equals = c.size() > 0;
    for (uint i = 1; i < c.size() and equals; ++i)
        equals = c[i-1] == c[i];
    return equals;
    
}


void deleteClause(uint n, int &repeats, const bool print) {
    ++repeats;
    if (print) {
        cout << "Deleted clause: ";
        printClause(clauses[n]);
        cout << endl;
        
    }
    clauses.erase(clauses.begin()+n);
    --numClauses;
    
}


void deleteUselessClauses(const bool print) {
  int repeats = 0;
  if (print) cout << endl << numClauses << " clauses to test" << endl;
  if (print) cout << "Searching useless clauses..." << endl;
  
  if (tautologyTest(clauses[0])) deleteClause(0, repeats, print);  
  for (uint i = 1; i < clauses.size(); ++i) {
      if (clauses[i-1] == clauses[i]) {
          deleteClause(i, repeats, print);
      }
  }  
  if (print) cout << "Useless clauses = " << repeats << endl;    
    
}


void generateAbsOccursList(const bool print) {
    absOccursList.resize(numVars + 1);    
    for (uint i = 0; i < clauses.size(); ++i) {        
        for (uint j = 0; j < clauses[i].size(); ++j) {
            absOccursList[abs(clauses[i][j])].literal = abs(clauses[i][j]);
            absOccursList[abs(clauses[i][j])].occurs.push_back(i);
        }        
        
    }
    absOccursListOrderedBySize = absOccursList;
    sort(absOccursListOrderedBySize.begin(), absOccursListOrderedBySize.end(), &sortByAbsOccurs);
        
    if (print) {
        for (uint i = 0; i < absOccursListOrderedBySize.size(); ++i) {
            cout << absOccursListOrderedBySize[i].occurs.size() << " times of the literal " << absOccursListOrderedBySize[i].literal << " in : ";
            for (uint j = 0; j < absOccursListOrderedBySize[i].occurs.size(); ++j) {
                printClause(clauses[absOccursListOrderedBySize[i].occurs[j]]);
                cout << " - ";
            
            }
            cout << endl;
        
        }
        
    }
    
}

// Función errónea, hay que replantear.
bool searchingDirectContradictions(const bool print) {
    if (print) cout << endl << "Searching direct contradictions..." << endl;
    int x = 0;
    int y = clauses.size() - 1;
    int contradictions = 0;
    for (uint i = 0; i < absOccursList.size(); ++i) {
        for (uint j = 1; j < absOccursList[i].occurs.size(); ++j) {
            if (absOccursList[i].occurs[j-1] == absOccursList[i].occurs[j]) {
                cout << "Same literal on one clause" << endl;
                for (uint ii = 0; ii < clauses[absOccursList[i].occurs[j-1]].size(); ++ii) {
                    for (uint jj = 0; jj < clauses[absOccursList[i].occurs[j]].size(); ++jj) {
                        if (abs(clauses[absOccursList[i].occurs[j-1]][ii]) == abs(clauses[absOccursList[i].occurs[j]][jj])) {
                            if (clauses[absOccursList[i].occurs[j-1]][ii] == -clauses[absOccursList[i].occurs[j]][jj]) {
                                if (print) {
                                    cout << "Contradiction on clause:" << endl;
                                    printClause(clauses[absOccursList[i].occurs[j]]);
                                    cout << endl;
                                }
                                ++contradictions;
                                
                            } else if (print) cout << "    No Contradiction" << endl;
                            
                        }
                        
                    }
                    
                }
                
            }
            
        }
        
    }
    
    while(x < y) {
        while (sortingClauses(clauses[y], invertClause(clauses[x]))) ++x;
        while (sortingClauses(invertClause(clauses[x]), clauses[y])) --y;
        if (clauses[x] == invertClause(clauses[y])) {
            ++contradictions;
            if (print) {
                cout << "Contradiction :" << endl;
                printClause(clauses[x]);
                cout << endl;
                printClause(clauses[y]);
                cout << endl;                
                
            }
            
        }   
        
    }  
    if (print) cout << "Number of contradictions = " << contradictions << endl;
    return contradictions > 0;    
    
}


void searchClausesGroups(const bool print) {
    vector<bool> addedLit = vector<bool>(numVars + 1, false);
    addedLit[0] = true;
    vector<bool> addedClauses = vector<bool>(numClauses, false);
    stack<int> litStack;
    
    int clausesToDrop = numClauses;
    while(clausesToDrop > 0) {
        clausesGroup cg;
        clausesGroups.push_back(cg);
        
        clausesGroups[clausesGroups.size() - 1].clauses.clear();
        clausesGroups[clausesGroups.size() - 1].litsIn.clear();
        
        vector<bool> stackedLit = vector<bool>(numVars + 1, false);
        stackedLit[0] = true;
        
        // initial seed of literals tree.        
        uint initClause = 0;
        while (addedClauses[initClause]) ++initClause;
        
        if (print) {
            cout << "Create group number " << clausesGroups.size() << "." << endl;
            
        }

        clause c = clauses[initClause];
        while (!litStack.empty()) litStack.pop();
        for (uint i =0; i < c.size(); ++i) {
            if (!addedLit[abs(c[i])] and !stackedLit[abs(c[i])]) {
                litStack.push(abs(c[i]));
                stackedLit[abs(c[i])] = true;
            }
        }
        
        // start to take connected lits
        while (!litStack.empty()) {
            while (!litStack.empty() and addedLit[litStack.top()]) litStack.pop();            
            if (!litStack.empty()) {
                uint lit = litStack.top();
                stack<int> litsToStack;               
                
                addedLit[lit] = true;
                clausesGroups[clausesGroups.size() - 1].litsIn.push_back(lit);
                for (uint i = 0; i < absOccursList[lit].occurs.size(); ++i) {
                    while (i < absOccursList[lit].occurs.size() and addedClauses[absOccursList[lit].occurs[i]]) ++i;
                    if (i < absOccursList[lit].occurs.size()) {
                        uint clauseNum = absOccursList[lit].occurs[i];
                        /*
                        if (print) {
                            cout << "adding clause num: " << clauseNum  << " - ";
                            printClause(clauses[clauseNum]);
                            cout << endl;                        
                            
                        }*/
                        
                        addedClauses[clauseNum] = true;
                        clause clauseToTake = clauses[clauseNum];
                        --clausesToDrop;                        
                        for (uint k = 0; k < clauseToTake.size(); ++k) {                            
                            int innerLit = clauseToTake[k];
                            if (!addedLit[abs(innerLit)]) {
                                litsToStack.push(abs(innerLit));
                            }
                            
                        }
                        
                        clausesGroups[clausesGroups.size() - 1].clauses.push_back(clauseToTake);                        
                        
                    }   
                    
                }
                
                litStack.pop();
                while (!litsToStack.empty()) {
                    if (!addedLit[litsToStack.top()] and !stackedLit[litsToStack.top()]) {
                        litStack.push(litsToStack.top());
                        stackedLit[litsToStack.top()] = true;
                    }
                    litsToStack.pop();
                    
                }                
                
            }            
            
        }        
        
        int pendingClauses = 0;
        for (uint i = 0; i < addedClauses.size(); ++i) {            
            if (!addedClauses[i]) {                
                ++pendingClauses;
                
            }
            
        }               
        
    }
    if (print) cout << "There hare " << clausesGroups.size() << " groups of clauses." << endl;
    
}


void generateOccursList(const bool print) {
    occursList.resize(numVars + 1);
    for (uint i = 0; i < clauses.size(); ++i) {        
        for (uint j = 0; j < clauses[i].size(); ++j) {
            occursList[abs(clauses[i][j])].literal = abs(clauses[i][j]);
            if (clauses[i][j] > 0) occursList[abs(clauses[i][j])].occursPos.push_back(i);
            if (clauses[i][j] < 0) occursList[abs(clauses[i][j])].occursNeg.push_back(i);
        }        
        
    }
    
    occursListOrderedBySize = occursList;
    sort(occursListOrderedBySize.begin(), occursListOrderedBySize.end(), &sortByOccurs);
    occursListOrderedBySize.erase(occursListOrderedBySize.end() -1);    
    
        
    if (print) {
        for (uint i = 0; i < occursListOrderedBySize.size(); ++i) {
            cout << occursListOrderedBySize[i].occursPos.size() + occursListOrderedBySize[i].occursNeg.size() << " times of the literal " << occursListOrderedBySize[i].literal << " in : ";
            for (uint j = 0; j < occursListOrderedBySize[i].occursPos.size(); ++j) {
                printClause(clauses[occursListOrderedBySize[i].occursPos[j]]);
                cout << " - ";
            
            }
            for (uint j = 0; j < occursListOrderedBySize[i].occursNeg.size(); ++j) {
                printClause(clauses[occursListOrderedBySize[i].occursNeg[j]]);
                cout << " - ";
            
            }
            cout << endl;
        
        }
        
    }
    
}


void readClauses( ) {
    // Skip comments
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
        
    }    
    // Read "cnf numVars numClauses"
    string aux;
    cin >> aux >> numVars >> numClauses;
    model.resize(numVars+1,UNDEF);   
    clauses.resize(numClauses);
    
    // Read clauses
    for (uint i = 0; i < numClauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) {
            clauses[i].push_back(lit);
            sort(clauses[i].begin(), clauses[i].end());
            
        }
        
    }  
   
}


int currentValueInModel(int lit) {
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        else return 1 - model[-lit];
        
    }
    
}


void setLiteralToTrue(int lit) {
    modelStack.push_back(lit);
    if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;
    
}


bool propagateGivesConflict () {
    while (indexOfNextLitToPropagate < modelStack.size() ) {
        int decisionLit;
        decisionLit = modelStack[indexOfNextLitToPropagate];                       
        
        ++indexOfNextLitToPropagate;        
        
        vector<uint> opositeClauses;
        if (decisionLit > 0) opositeClauses = occursList[abs(decisionLit)].occursNeg;
        else opositeClauses = occursList[abs(decisionLit)].occursPos;                
        for (uint i = 0; i < opositeClauses.size(); ++i) {
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;            
            for (uint k = 0; not someLitTrue and k < clauses[opositeClauses[i]].size(); ++k){
                int val = currentValueInModel(clauses[opositeClauses[i]][k]);
                if (val == TRUE) someLitTrue = true;
                else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[opositeClauses[i]][k]; }
                
            }
            if (not someLitTrue and numUndefs == 0) {
                for (uint k = 0; k< clauses[opositeClauses[i]].size(); ++k) {
                    ++conflictLits[abs(clauses[opositeClauses[i]][k])];
                }
                auto maxCounter = max_element(conflictLits.begin(), conflictLits.end());
                if (conflictLits[*maxCounter] > numVars) {
                    //cout << "Maximo conflictos con: " << conflictLits[*maxCounter] << endl;
                    for (uint k = 0; k < conflictLits.size(); ++k) {                        
                        conflictLits[k] /= 2 ;
                        //if (conflictLits[k]) cout << "Conflictos con el lit " << k << ": " << conflictLits[k] << endl;
                        
                    }
                }
                return true; // conflict! all lits false
                
            }
            else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);
            
        }        
        
    }    
    return false;
    
}


void backtrack() {
    //cout << "Inicia backtrack" << endl;
    uint i = modelStack.size() -1;
    int lit = 0;
    while (modelStack[i] != 0) { // 0 is the DL mark
        lit = modelStack[i];
        model[abs(lit)] = UNDEF;
        modelStack.pop_back();
        --i;
        
    }
    
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    indexOfNextLitToPropagate = modelStack.size();
    setLiteralToTrue(-lit);  // reverse last decision
    
}


// Heuristic for finding the next decision literal:
int getNextDecisionLiteral() {
    ++decisionCounter;
    vector<uint> searchConflict = conflictLits;
    auto maxCounter = max_element(searchConflict.begin(), searchConflict.end());
    while (searchConflict[*maxCounter] > numVars / 2) {
        for (uint i = 1; i <= searchConflict.size(); ++i) {
            if (model[distance(searchConflict.begin(), maxCounter)] == UNDEF) {
                ++conflictDecisions;
                return distance(searchConflict.begin(), maxCounter); 
            } else {
                searchConflict[*maxCounter] = 0;
                maxCounter = max_element(searchConflict.begin(), searchConflict.end());
            }
        }
        
    }    
    
    for (uint i = 1; i <= occursListOrderedBySize.size(); ++i) {
        if (model[occursListOrderedBySize[i].literal] == UNDEF) return occursListOrderedBySize[i].literal;      
        
    }
    --decisionCounter;
    return 0; // reurns 0 when all literals are defined
    
}


void checkmodel(){
  for (uint i = 0; i < numClauses; ++i){
    bool someTrue = false;
    for (uint j = 0; not someTrue and j < clauses[i].size(); ++j)
      someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
    if (not someTrue) {
      cout << "Error in model, clause is not satisfied:";
      for (uint j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
      cout << endl;
      exit(1);
    }
  }  
}

int main() { 
    readClauses(); // reads numVars, numClauses and clauses  
    model.resize(numVars+1,UNDEF);
    conflictLits.resize(numVars+1, 0);
    indexOfNextLitToPropagate = 0;  
    decisionLevel = 0;
    decisionCounter = 0;
    conflictDecisions= 0;
    
    // Cost of sort algorithm with numClauses elements
    sort(clauses.begin(), clauses.end(), &sortingClauses);
    
    // Cost: O(numClauses) if clauses are ordered;71
    deleteUselessClauses(true);
    
    // Not necessary
    //generateAbsOccursList(false);
    
    // Cost: O(numClauses) if clauses are ordered;
    //if (searchingDirectContradictions(true)) { cout << "UNSATISFIABLE" << endl; return 10; }
    
    //Every problems with 1 group
    //searchClausesGroups(false);
    
    generateOccursList(false);
    
    // Take care of initial unit clauses, if any
    for (uint i = 0; i < numClauses; ++i) {
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = currentValueInModel(lit);
            if (val == FALSE) {cout << "UNSATISFIABLE" << endl; return 10;}
            else if (val == UNDEF) setLiteralToTrue(lit);
           
        }
        
    }
    
    // DPLL algorithm
    while (true) {
        while (propagateGivesConflict()) {
            if (decisionLevel == 0) {                
                cout << "UNSATISFIABLE" << endl;
                printStats();
                return 10;
                
            }
            backtrack();
            
        }
        
        int decisionLit = getNextDecisionLiteral();
        if (decisionLit == 0) {
            checkmodel();            
            cout << "SATISFIABLE" << endl;
            printStats();
            return 20;
            
        }
        
        // start new decision level:
        modelStack.push_back(0);  // push mark indicating new DL
        ++indexOfNextLitToPropagate;
        ++decisionLevel;
        setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
        
        
    }
    
}

/*
a b c
a c b
b c a
b a c
c a b
c b a


Separar occurs lists + y -

contador de variables conflictivas
dividir contadores periodicamente
*/
