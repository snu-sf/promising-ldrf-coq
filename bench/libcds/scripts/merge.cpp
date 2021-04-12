#include <iostream>
#include <fstream>
#include <map>
#include <vector>
#include <string>
#include <cstring>
#include <algorithm>
#include <math.h>

using namespace std;


int main(int argc, char** argv) {
  if (argc == 2) {
    ofstream outfile;
    outfile.open(string(argv[1]) + "/stat.csv");

    outfile << "cases," << endl;
    outfile << "average," << endl;
    outfile << "stdev," << endl;
    outfile << "normalized_average," << endl;
    outfile << "normalized_stdev," << endl;
    outfile.close();
    return 0;
  }
  else if (argc != 3) {
    exit(1);
  }

  ifstream infile;
  infile.open(string(argv[2]));

  ifstream origfile;
  origfile.open(string(argv[1]) + "/stat.csv");

  string orig_tests;
  string orig_average;
  string orig_stdev;
  string new_tests;
  string new_average;
  string new_stdev;

  origfile >> orig_tests;
  origfile >> orig_average;
  origfile >> orig_stdev;

  infile >> new_tests;
  infile >> new_average;
  infile >> new_stdev;

  infile.close();
  origfile.close();

  ofstream outfile;
  outfile.open(string(argv[1]) + "/stat.csv");

  outfile << orig_tests + new_tests << endl;
  outfile << orig_average + new_average << endl;
  outfile << orig_stdev + new_stdev << endl;

  outfile.close();
  return 0;
}
