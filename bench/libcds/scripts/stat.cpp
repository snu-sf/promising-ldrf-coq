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
  ofstream outfile;
  outfile.open(string(argv[1]) + "/stat.csv");

  if (argc != 4) {
    exit(1);
  }

  int num = std::stoi(argv[2]) - 2 * std::stoi(argv[3]);

  vector<string> tests;
  vector<double> ref_mean;
  vector<double> ref_stdev;
  vector<double> fake_mean;
  vector<double> fake_stdev;
  vector<double> cmp_mean;
  vector<double> cmp_stdev;

  string line;

  ifstream ref_file, fake_file, cmp_file;

  // ref
  ref_file.open(string(argv[1]) + "/ref/stat.csv");
  fake_file.open(string(argv[1]) + "/fake/stat.csv");
  cmp_file.open(string(argv[1]) + "/cmp/stat.csv");

  // testcase
  ref_file >> line; 
  {
    char* chr = strdup(line.c_str());
    strtok(chr, ",");
    char *tmp = strtok(NULL, ",");
    while (tmp != NULL) {
      tests.emplace_back(string(tmp));
      tmp = strtok(NULL, ",");
    }
    free(chr);
  }

  // average
  ref_file >> line; 
  {
    char* chr = strdup(line.c_str());
    strtok(chr, ",");
    char *tmp = strtok(NULL, ",");
    while (tmp != NULL) {
      ref_mean.emplace_back(stod(tmp));
      tmp = strtok(NULL, ",");
    }
    free(chr);
  }

  // standard deviation
  ref_file >> line; 
  {
    char* chr = strdup(line.c_str());
    strtok(chr, ",");
    char *tmp = strtok(NULL, ",");
    while (tmp != NULL) {
      ref_stdev.emplace_back(stod(tmp));
      tmp = strtok(NULL, ",");
    }
    free(chr);
  }


  // fake
  fake_file >> line; 

  // average
  fake_file >> line; 
  {
    char* chr = strdup(line.c_str());
    strtok(chr, ",");
    char *tmp = strtok(NULL, ",");
    while (tmp != NULL) {
      fake_mean.emplace_back(stod(tmp));
      tmp = strtok(NULL, ",");
    }
    free(chr);
  }

  // standard deviation
  fake_file >> line; 
  {
    char* chr = strdup(line.c_str());
    strtok(chr, ",");
    char *tmp = strtok(NULL, ",");
    while (tmp != NULL) {
      fake_stdev.emplace_back(stod(tmp));
      tmp = strtok(NULL, ",");
    }
    free(chr);
  }


  // cmp
  cmp_file >> line; 

  // average
  cmp_file >> line; 
  {
    char* chr = strdup(line.c_str());
    strtok(chr, ",");
    char *tmp = strtok(NULL, ",");
    while (tmp != NULL) {
      cmp_mean.emplace_back(stod(tmp));
      tmp = strtok(NULL, ",");
    }
    free(chr);
  }

  // standard deviation
  cmp_file >> line; 
  {
    char* chr = strdup(line.c_str());
    strtok(chr, ",");
    char *tmp = strtok(NULL, ",");
    while (tmp != NULL) {
      cmp_stdev.emplace_back(stod(tmp));
      tmp = strtok(NULL, ",");
    }
    free(chr);
  }


  // test case
  {
    outfile << ",";
    for(auto it = tests.begin(); it != tests.end(); it++) {
      outfile << *it << ",,,";
    }
    outfile << endl;
  }

  {
    outfile << ",";
    for(auto it = tests.begin(); it != tests.end(); it++) {
      outfile << "ref,fake,cmp,";
    }
    outfile << endl;
  }

  {
    outfile << "average,";
    int i = 0;
    for(auto it = tests.begin(); it != tests.end(); it++) {
      outfile << ref_mean[i] << "," << fake_mean[i] << "," << cmp_mean[i] << ",";
      i++;
    }
    outfile << endl;
  }

  {
    outfile << "stdev,";
    int i = 0;
    for(auto it = tests.begin(); it != tests.end(); it++) {
      outfile << ref_stdev[i] << "," << fake_stdev[i] << "," << cmp_stdev[i] << ",";
      i++;
    }
    outfile << endl;
  }

  {
    outfile << "normalized_average,";
    int i = 0;
    for(auto it = tests.begin(); it != tests.end(); it++) {
      outfile << (ref_mean[i] / ref_mean[i]) << "," << (fake_mean[i] / ref_mean[i]) << "," << (cmp_mean[i] / ref_mean[i]) << ",";
      i++;
    }
    outfile << endl;
  }

  {
    outfile << "normalized_stdev,";
    int i = 0;
    for(auto it = tests.begin(); it != tests.end(); it++) {
      outfile << (ref_stdev[i] / ref_mean[i]) << "," << (fake_stdev[i] / ref_mean[i]) << "," << (cmp_stdev[i] / ref_mean[i]) << ",";
      i++;
    }
    outfile << endl;
  }

  ref_file.close();
  fake_file.close();
  cmp_file.close();
  outfile.close();
  return 0;
}
