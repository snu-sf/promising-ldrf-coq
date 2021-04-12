#include <iostream>
#include <fstream>
#include <map>
#include <vector>
#include <string>
#include <algorithm>
#include <math.h>

using namespace std;


int main(int argc, char** argv) {
  if (argc != 6) {
    cout << "usage: " << argv[0] << " dir filename outdir runs discard" << endl;
    exit(1);
  }

  int runs = std::stoi(argv[4]);
  int discard = std::stoi(argv[5]);

  map<string,vector<int>*> tests;
  map<string, double> means;
  map<string, double> stdevs;

  ifstream infile;
  infile.open(string(argv[1])+"/"+string(argv[2]));

  string test, time;

  // read data
  while (infile >> test >> time) {
    auto it = tests.find(test);

    if (it != tests.end()) {
      it->second->emplace_back(stoi(time));
      continue;
    }

    tests.insert(pair<string,vector<int>*>(test, new vector<int>()));
    tests.find(test)->second->emplace_back(stoi(time));
  }

  ofstream outfile;
  outfile.open(string(argv[3]) + "/" + string(argv[2]) + ".stat.csv");

  for (auto& x: tests) {
    outfile << x.first << ",";
    sort(x.second->begin(), x.second->end());
    
    double sum = 0;
    double sumsquare = 0;
    for (int i = discard; i < runs - discard; i++) {
      sum += (*x.second)[i];
      sumsquare += (double)(*x.second)[i] * (*x.second)[i];
    }
    
    // arithmetic mean
    means[x.first] = sum / (runs - 2 * discard);
    // sample standard deviation
    stdevs[x.first] = sqrt(sumsquare/(runs - 2 * discard - 1) - sum * sum / (runs - 2 * discard) / (runs - 2 * discard - 1));
  }
  outfile << "\n";

  for (auto& x: tests) {
    outfile << means[x.first] << ",";
  }
  outfile << "\n";

  for (auto& x: tests) {
    outfile << stdevs[x.first] << ",";
  }
  outfile << "\n";

  for (int i = discard; i < runs - discard; i++) { // discard the fastest and the slowest
    for (auto& x: tests) {
      outfile << (*x.second)[i] << ",";
    }
    outfile << "\n";
  }

  infile.close();
  outfile.close();
  return 0;
}
