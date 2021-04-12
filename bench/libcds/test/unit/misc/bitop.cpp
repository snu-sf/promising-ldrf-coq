// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#include <cds_test/ext_gtest.h>

#include <cds/algo/int_algo.h>
//#include <cds/details/bit_reverse_counter.h>

namespace {
    class bitop : public ::testing::Test
    {};

    TEST_F( bitop, bitop32 )
    {
        uint32_t n = 0;

        EXPECT_EQ( cds::bitop::MSB(n), 0 ) << "n=" << n;
        EXPECT_EQ( cds::bitop::LSB( n ), 0 ) << "n=" << n;
        EXPECT_EQ( cds::bitop::SBC( n ), 0 ) << "n=" << n;
        EXPECT_EQ( cds::bitop::ZBC( n ), static_cast<int>( sizeof( n ) * 8 )) << "n=" << n;

        int nBit = 1;
        for ( n = 1; n != 0; n *= 2 ) {
            EXPECT_EQ( cds::bitop::MSB( n ), nBit ) << "n=" << n;
            EXPECT_EQ( cds::bitop::LSB( n ), nBit ) << "n=" << n;
            EXPECT_EQ( cds::bitop::MSBnz( n ), nBit - 1 ) << "n=" << n;
            EXPECT_EQ( cds::bitop::LSBnz( n ), nBit - 1 ) << "n=" << n;
            EXPECT_EQ( cds::bitop::SBC( n ), 1 ) << "n=" << n;
            EXPECT_EQ( cds::bitop::ZBC( n ), static_cast<int>( sizeof( n ) * 8 - 1 )) << "n=" << n;

            ++nBit;
        }
    }

    TEST_F( bitop, bitop64 )
    {
        uint64_t n = 0;

        EXPECT_EQ( cds::bitop::MSB( n ), 0 ) << "n=" << n;
        EXPECT_EQ( cds::bitop::LSB( n ), 0 ) << "n=" << n;
        EXPECT_EQ( cds::bitop::SBC( n ), 0 ) << "n=" << n;
        EXPECT_EQ( cds::bitop::ZBC( n ), static_cast<int>( sizeof( n ) * 8 )) << "n=" << n;

        int nBit = 1;
        for ( n = 1; n != 0; n *= 2 ) {
            EXPECT_EQ( cds::bitop::MSB( n ), nBit ) << "n=" << n;
            EXPECT_EQ( cds::bitop::LSB( n ), nBit ) << "n=" << n;
            EXPECT_EQ( cds::bitop::MSBnz( n ), nBit - 1 ) << "n=" << n;
            EXPECT_EQ( cds::bitop::LSBnz( n ), nBit - 1 ) << "n=" << n;
            EXPECT_EQ( cds::bitop::SBC( n ), 1 ) << "n=" << n;
            EXPECT_EQ( cds::bitop::ZBC( n ), static_cast<int>( sizeof( n ) * 8 - 1 )) << "n=" << n;

            ++nBit;
        }
    }

    TEST_F( bitop, floor_pow2 )
    {
        EXPECT_EQ( cds::beans::floor2( 0u ), 1u );
        EXPECT_EQ( cds::beans::floor2( 1u ), 1u );
        EXPECT_EQ( cds::beans::floor2( 2u ), 2u );
        EXPECT_EQ( cds::beans::floor2( 3u ), 2u );
        EXPECT_EQ( cds::beans::floor2( 4u ), 4u );
        EXPECT_EQ( cds::beans::floor2( 5u ), 4u );
        EXPECT_EQ( cds::beans::floor2( 7u ), 4u );
        EXPECT_EQ( cds::beans::floor2( 8u ), 8u );
        EXPECT_EQ( cds::beans::floor2( 9u ), 8u );

        for ( uint32_t n = 2; n; n <<= 1 )
        {
            EXPECT_EQ( cds::beans::floor2( n - 1 ), n / 2 );
            EXPECT_EQ( cds::beans::floor2( n + 1 ), n );
        }

        for ( uint64_t n = 2; n; n <<= 1 )
        {
            EXPECT_EQ( cds::beans::floor2( n - 1 ), n / 2 );
            EXPECT_EQ( cds::beans::floor2( n ), n );
            EXPECT_EQ( cds::beans::floor2( n + 1 ), n );
        }
    }

    TEST_F( bitop, ceil_pow2 )
    {
        EXPECT_EQ( cds::beans::ceil2( 0u ), 1u );
        EXPECT_EQ( cds::beans::ceil2( 1u ), 1u );
        EXPECT_EQ( cds::beans::ceil2( 2u ), 2u );
        EXPECT_EQ( cds::beans::ceil2( 3u ), 4u );
        EXPECT_EQ( cds::beans::ceil2( 4u ), 4u );
        EXPECT_EQ( cds::beans::ceil2( 5u ), 8u );
        EXPECT_EQ( cds::beans::ceil2( 7u ), 8u );
        EXPECT_EQ( cds::beans::ceil2( 8u ), 8u );
        EXPECT_EQ( cds::beans::ceil2( 9u ), 16u );

        for ( uint32_t n = 4; n < (uint32_t(1) << 31); n <<= 1 )
        {
            EXPECT_EQ( cds::beans::ceil2( n - 1 ), n );
            EXPECT_EQ( cds::beans::ceil2( n ), n );
            EXPECT_EQ( cds::beans::ceil2( n + 1 ), n * 2 );
        }

        for ( uint64_t n = 4; n < (uint64_t(1) << 63); n <<= 1 )
        {
            EXPECT_EQ( cds::beans::ceil2( n - 1 ), n );
            EXPECT_EQ( cds::beans::ceil2( n ), n );
            EXPECT_EQ( cds::beans::ceil2( n + 1 ), n * 2 );
        }
    }

    /*
    TEST_F( bitop, bit_reverse_counter )
    {
        cds::bitop::bit_reverse_counter<> c;

        while ( c.value() < 8 ) {
            size_t res = c.inc();
            std::cout << "inc result: " << res
                      << " value: " << c.value()
                      << " reversed: " << c.reversed_value()
                      << " high_bit: " << c.high_bit() << "\n";
        }

        while ( c.value() > 0 ) {
            size_t res = c.dec();
            std::cout << "dec result: " << res
                << " value: " << c.value()
                << " reversed: " << c.reversed_value()
                << " high_bit: " << c.high_bit() << "\n";
        }
    }
    */

} // namespace
