// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#include "map_insdel_func.h"

namespace map {

    size_t Map_InsDel_func::s_nMapSize = 1000000;      // map size
    size_t Map_InsDel_func::s_nInsertThreadCount = 4;  // count of insertion thread
    size_t Map_InsDel_func::s_nDeleteThreadCount = 4;  // count of deletion thread
    size_t Map_InsDel_func::s_nUpdateThreadCount = 4;  // count of ensure thread
    size_t Map_InsDel_func::s_nThreadPassCount = 4;    // pass count for each thread
    size_t Map_InsDel_func::s_nMaxLoadFactor = 8;      // maximum load factor

    size_t Map_InsDel_func::s_nCuckooInitialSize = 1024;// initial size for CuckooSet
    size_t Map_InsDel_func::s_nCuckooProbesetSize = 16; // CuckooSet probeset size (only for list-based probeset)
    size_t Map_InsDel_func::s_nCuckooProbesetThreshold = 0; // CUckooSet probeset threshold (0 - use default)

    size_t Map_InsDel_func::s_nFeldmanMap_HeadBits = 10;
    size_t Map_InsDel_func::s_nFeldmanMap_ArrayBits = 4;

    size_t Map_InsDel_func::s_nLoadFactor = 1;
    Map_InsDel_func::key_array Map_InsDel_func::s_arrKeys;

    void Map_InsDel_func::SetUpTestCase()
    {
        cds_test::config const& cfg = get_config( "map_insdel_func" );

        s_nMapSize = cfg.get_size_t( "MapSize", s_nMapSize );
        if ( s_nMapSize < 1000 )
            s_nMapSize = 1000;

        s_nInsertThreadCount = cfg.get_size_t( "InsertThreadCount", s_nInsertThreadCount );
        if ( s_nInsertThreadCount == 0 )
            s_nInsertThreadCount = 2;

        s_nDeleteThreadCount = cfg.get_size_t( "DeleteThreadCount", s_nDeleteThreadCount );
        if ( s_nDeleteThreadCount == 0 )
            s_nDeleteThreadCount = 2;

        s_nUpdateThreadCount = cfg.get_size_t( "UpdateThreadCount", s_nUpdateThreadCount );
        //if ( s_nUpdateThreadCount == 0 )
        //    s_nUpdateThreadCount = 2;

        s_nThreadPassCount = cfg.get_size_t( "ThreadPassCount", s_nThreadPassCount );
        if ( s_nThreadPassCount == 0 )
            s_nThreadPassCount = 4;

        s_nMaxLoadFactor = cfg.get_size_t( "MaxLoadFactor", s_nMaxLoadFactor );
        if ( s_nMaxLoadFactor == 0 )
            s_nMaxLoadFactor = 1;

        s_nCuckooInitialSize = cfg.get_size_t( "CuckooInitialSize", s_nCuckooInitialSize );
        if ( s_nCuckooInitialSize < 256 )
            s_nCuckooInitialSize = 256;

        s_nCuckooProbesetSize = cfg.get_size_t( "CuckooProbesetSize", s_nCuckooProbesetSize );
        if ( s_nCuckooProbesetSize < 8 )
            s_nCuckooProbesetSize = 8;

        s_nCuckooProbesetThreshold = cfg.get_size_t( "CuckooProbesetThreshold", s_nCuckooProbesetThreshold );

        s_nFeldmanMap_HeadBits = cfg.get_size_t( "FeldmanMapHeadBits", s_nFeldmanMap_HeadBits );
        if ( s_nFeldmanMap_HeadBits == 0 )
            s_nFeldmanMap_HeadBits = 2;

        s_nFeldmanMap_ArrayBits = cfg.get_size_t( "FeldmanMapArrayBits", s_nFeldmanMap_ArrayBits );
        if ( s_nFeldmanMap_ArrayBits == 0 )
            s_nFeldmanMap_ArrayBits = 2;

        s_arrKeys.clear();
        s_arrKeys.reserve( s_nMapSize );
        for ( size_t i = 0; i < s_nMapSize; ++i )
            s_arrKeys.push_back( i );
        shuffle( s_arrKeys.begin(), s_arrKeys.end());
    }

    void Map_InsDel_func::TearDownTestCase()
    {
        s_arrKeys.clear();
    }

    std::vector<size_t> Map_InsDel_func_LF::get_load_factors()
    {
        cds_test::config const& cfg = get_config( "map_insdel_func" );

        s_nMaxLoadFactor = cfg.get_size_t( "MaxLoadFactor", s_nMaxLoadFactor );
        if ( s_nMaxLoadFactor == 0 )
            s_nMaxLoadFactor = 1;

        std::vector<size_t> lf;
        for ( size_t n = 1; n <= s_nMaxLoadFactor; n *= 2 )
            lf.push_back( n );

        return lf;
    }

#ifdef CDSTEST_GTEST_INSTANTIATE_TEST_CASE_P_HAS_4TH_ARG
    static std::string get_test_parameter_name( testing::TestParamInfo<size_t> const& p )
    {
        return std::to_string( p.param );
    }
    INSTANTIATE_TEST_CASE_P( a, Map_InsDel_func_LF, ::testing::ValuesIn( Map_InsDel_func_LF::get_load_factors()), get_test_parameter_name );
#else
    INSTANTIATE_TEST_CASE_P( a, Map_InsDel_func_LF, ::testing::ValuesIn( Map_InsDel_func_LF::get_load_factors()));
#endif

} // namespace map
