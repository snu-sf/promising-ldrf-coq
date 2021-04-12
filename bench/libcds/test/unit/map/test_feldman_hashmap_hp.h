// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef CDSUNIT_MAP_TEST_FELDMAN_HASHMAP_HP_H
#define CDSUNIT_MAP_TEST_FELDMAN_HASHMAP_HP_H

#include "test_feldman_hashmap.h"

namespace cds_test {

    class feldman_hashmap_hp: public feldman_hashmap
    {
        typedef feldman_hashmap base_class;

    protected:
        template <class Map>
        void test( Map& m )
        {
            // Precondition: map is empty
            // Postcondition: map is empty

            base_class::test( m );

            ASSERT_TRUE( m.empty());
            ASSERT_CONTAINER_SIZE( m, 0 );

            //typedef typename Map::value_type map_pair;
            size_t const kkSize = base_class::kSize;

            typedef typename Map::key_type key_type;
            typedef typename Map::mapped_type value_type;

            std::vector<key_type> arrKeys;
            for ( int i = 0; i < static_cast<int>(kkSize); ++i )
                arrKeys.push_back( key_type( i ));
            shuffle( arrKeys.begin(), arrKeys.end());

            std::vector< value_type > arrVals;
            for ( size_t i = 0; i < kkSize; ++i ) {
                value_type val;
                val.nVal = static_cast<int>( i );
                val.strVal = std::to_string( i );
                arrVals.push_back( val );
            }

            for ( auto const& i : arrKeys )
                ASSERT_TRUE( m.insert( i ));
            ASSERT_FALSE( m.empty());
            ASSERT_CONTAINER_SIZE( m, kkSize );

            // iterators
            size_t nCount = 0;
            for ( auto it = m.begin(); it != m.end(); ++it ) {
                EXPECT_EQ( it->second.nVal, 0 );
                it->second.nVal = it->first.nKey * 2;
                ++nCount;
            }
            EXPECT_EQ( nCount, kkSize );

            nCount = 0;
            for ( auto it = m.cbegin(); it != m.cend(); ++it ) {
                EXPECT_EQ( it->second.nVal, it->first.nKey * 2 );
                ++nCount;
            }
            EXPECT_EQ( nCount, kkSize );

            nCount = 0;
            for ( auto it = m.rbegin(); it != m.rend(); ++it ) {
                EXPECT_EQ( it->second.nVal, it->first.nKey * 2 );
                it->second.nVal = it->first.nKey * 4;
                ++nCount;
            }
            EXPECT_EQ( nCount, kkSize );

            nCount = 0;
            for ( auto it = m.crbegin(); it != m.crend(); ++it ) {
                EXPECT_EQ( it->second.nVal, it->first.nKey * 4 );
                ++nCount;
            }
            EXPECT_EQ( nCount, kkSize );

            // get/extract
            typedef typename Map::guarded_ptr guarded_ptr;
            guarded_ptr gp;

            for ( auto const& i : arrKeys ) {
                value_type const& val = arrVals.at( i.nKey );

                gp = m.get( i.nKey );
                ASSERT_FALSE( !gp );
                ASSERT_EQ( gp->first.nKey, i.nKey );
                gp.release();
                gp = m.get( i );
                ASSERT_FALSE( !gp );
                ASSERT_EQ( gp->first.nKey, i.nKey );
                gp.release();

                switch ( i.nKey % 3 ) {
                case 0:
                    gp = m.extract( i.nKey );
                    break;
                case 1:
                    gp = m.extract( i );
                    break;
                case 2:
                    gp = m.extract( val.strVal );
                    break;
                }
                ASSERT_FALSE( !gp );
                ASSERT_EQ( gp->first.nKey, i.nKey );
                gp.release();

                gp = m.get( i.nKey );
                ASSERT_TRUE( !gp );
                gp = m.get( i );
                ASSERT_TRUE( !gp );
            }
            ASSERT_TRUE( m.empty());
            ASSERT_CONTAINER_SIZE( m, 0 );

            // erase_at( iterator )
            for ( auto const& i : arrKeys )
                ASSERT_TRUE( m.insert( i ));
            ASSERT_FALSE( m.empty());
            ASSERT_CONTAINER_SIZE( m, kkSize );

            nCount = 0;
            for ( auto it = m.begin(); it != m.end(); ++it ) {
                EXPECT_EQ( it->second.nVal, 0 );
                ASSERT_TRUE( m.erase_at( it ));
                ++nCount;
            }
            EXPECT_EQ( nCount, kkSize );
            ASSERT_TRUE( m.empty());
            ASSERT_CONTAINER_SIZE( m, 0 );

            // erase_at( reverse_iterator )
            for ( auto const& i : arrKeys )
                ASSERT_TRUE( m.insert( i ));
            ASSERT_FALSE( m.empty());
            ASSERT_CONTAINER_SIZE( m, kkSize );

            nCount = 0;
            for ( auto it = m.rbegin(); it != m.rend(); ++it ) {
                EXPECT_EQ( it->second.nVal, 0 );
                ASSERT_TRUE( m.erase_at( it ));
                ++nCount;
            }
            EXPECT_EQ( nCount, kkSize );
            ASSERT_TRUE( m.empty());
            ASSERT_CONTAINER_SIZE( m, 0 );

            // erase_at( const_reverse_iterator )
            for ( auto const& i : arrKeys )
                ASSERT_TRUE( m.insert( i ));
            ASSERT_FALSE( m.empty());
            ASSERT_CONTAINER_SIZE( m, kkSize );

            nCount = 0;
            for ( auto it = m.crbegin(); it != m.crend(); ++it ) {
                EXPECT_EQ( it->second.nVal, 0 );
                ASSERT_TRUE( m.erase_at( it ));
                ++nCount;
            }
            EXPECT_EQ( nCount, kkSize );
            ASSERT_TRUE( m.empty());
            ASSERT_CONTAINER_SIZE( m, 0 );

            // erase_at( const_iterator )
            for ( auto const& i : arrKeys )
                ASSERT_TRUE( m.insert( i ));
            ASSERT_FALSE( m.empty());
            ASSERT_CONTAINER_SIZE( m, kkSize );

            nCount = 0;
            for ( auto it = m.cbegin(); it != m.cend(); ++it ) {
                EXPECT_EQ( it->second.nVal, 0 );
                ASSERT_TRUE( m.erase_at( it ));
                ++nCount;
            }
            EXPECT_EQ( nCount, kkSize );
            ASSERT_TRUE( m.empty());
            ASSERT_CONTAINER_SIZE( m, 0 );
        }
    };

} // namespace cds_test

#endif // #ifndef CDSUNIT_MAP_TEST_FELDMAN_HASHMAP_HP_H
