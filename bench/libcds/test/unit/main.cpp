// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#include <cds_test/ext_gtest.h>
#include <cds/init.h>

#include <cds_test/fixture.h>

namespace cds_test {
    /*static*/ std::random_device fixture::random_dev_;
    /*static*/ std::mt19937 fixture::random_gen_( random_dev_());
} // namespace cds_test

int main( int argc, char **argv )
{
    int result;
    cds::Initialize();
    {
        ::testing::InitGoogleTest( &argc, argv );
        result =  RUN_ALL_TESTS();
    }
    cds::Terminate();
    return result;
}
