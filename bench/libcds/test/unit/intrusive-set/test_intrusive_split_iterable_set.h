// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef CDSUNIT_SET_TEST_INTRUSIVE_SPLIT_ITERABLE_SET_H
#define CDSUNIT_SET_TEST_INTRUSIVE_SPLIT_ITERABLE_SET_H

#include <cds_test/check_size.h>
#include <cds_test/fixture.h>

#include <cds/opt/hash.h>
#include <functional>   // ref

// forward declaration
namespace cds { namespace intrusive {}}

namespace cds_test {

    namespace ci = cds::intrusive;
    namespace co = cds::opt;

    class intrusive_split_iterable_set: public fixture
    {
    public:
        static size_t const kSize = 100;

        struct stat
        {
            unsigned int nDisposeCount  ;   // count of disposer calling
            unsigned int nFindCount     ;   // count of find-functor calling
            unsigned int nUpdateNewCount;
            unsigned int nUpdateCount;
            mutable unsigned int nEraseCount;

            stat()
            {
                clear_stat();
            }

            void clear_stat()
            {
                memset( this, 0, sizeof( *this ));
            }
        };

        template <typename Base>
        struct item_type: public stat, public Base
        {
            int nKey;
            int nVal;

            item_type( int k )
                : nKey(k)
                , nVal(0)
            {}

            int key() const
            {
                return nKey;
            }
        };

        struct hash_int {
            size_t operator()( int i ) const
            {
                return co::v::hash<int>()( i );
            }
            template <typename Q>
            size_t operator()( Q const& i ) const
            {
                return (*this)( i.key());
            }
        };

        struct simple_item_counter {
            size_t  m_nCount;

            simple_item_counter()
                : m_nCount(0)
            {}

            size_t operator ++()
            {
                return ++m_nCount;
            }

            size_t operator --()
            {
                return --m_nCount;
            }

            void reset()
            {
                m_nCount = 0;
            }

            operator size_t() const
            {
                return m_nCount;
            }

        };


        template <typename T>
        struct less
        {
            bool operator ()(const T& v1, const T& v2 ) const
            {
                return v1.key() < v2.key();
            }

            template <typename Q>
            bool operator ()(const T& v1, const Q& v2 ) const
            {
                return v1.key() < v2;
            }

            template <typename Q>
            bool operator ()(const Q& v1, const T& v2 ) const
            {
                return v1 < v2.key();
            }
        };

        template <typename T>
        struct cmp {
            int operator ()(const T& v1, const T& v2 ) const
            {
                if ( v1.key() < v2.key())
                    return -1;
                return v1.key() > v2.key() ? 1 : 0;
            }

            template <typename Q>
            int operator ()(const T& v1, const Q& v2 ) const
            {
                if ( v1.key() < v2 )
                    return -1;
                return v1.key() > v2 ? 1 : 0;
            }

            template <typename Q>
            int operator ()(const Q& v1, const T& v2 ) const
            {
                if ( v1 < v2.key())
                    return -1;
                return v1 > v2.key() ? 1 : 0;
            }
        };

        struct other_item {
            int nKey;

            explicit other_item( int k )
                : nKey( k )
            {}

            int key() const
            {
                return nKey;
            }
        };

        struct other_less {
            template <typename Q, typename T>
            bool operator()( Q const& lhs, T const& rhs ) const
            {
                return lhs.key() < rhs.key();
            }
        };

        struct mock_disposer
        {
            template <typename T>
            void operator ()( T * p )
            {
                ++p->nDisposeCount;
            }
        };

    protected:
        template <class Set>
        void test( Set& s )
        {
            // Precondition: set is empty
            // Postcondition: set is empty

            ASSERT_TRUE( s.empty());
            ASSERT_CONTAINER_SIZE( s, 0 );
            size_t const nSetSize = kSize;

            typedef typename Set::value_type value_type;

            std::vector< value_type > data;
            std::vector< size_t> indices;
            data.reserve( kSize );
            indices.reserve( kSize );
            for ( size_t key = 0; key < kSize; ++key ) {
                data.push_back( value_type( static_cast<int>( key )));
                indices.push_back( key );
            }
            shuffle( indices.begin(), indices.end());

            // insert/find
            for ( auto idx : indices ) {
                auto& i = data[ idx ];

                ASSERT_FALSE( s.contains( i.nKey ));
                ASSERT_FALSE( s.contains( i ));
                ASSERT_FALSE( s.contains( other_item( i.key()), other_less()));
                ASSERT_FALSE( s.find( i.nKey, []( value_type&, int ) {} ));
                ASSERT_FALSE( s.find_with( other_item( i.key()), other_less(), []( value_type&, other_item const& ) {} ));
                ASSERT_TRUE( s.find( i.nKey ) == s.end());
                ASSERT_TRUE( s.find_with( other_item( i.key()), other_less()) == s.end());

                std::pair<bool, bool> updResult;

                updResult = s.update( i, []( value_type&, value_type* )
                {
                    ASSERT_TRUE( false );
                }, false );
                EXPECT_FALSE( updResult.first );
                EXPECT_FALSE( updResult.second );

                updResult = s.upsert( i, false );
                EXPECT_FALSE( updResult.first );
                EXPECT_FALSE( updResult.second );

                switch ( i.key() % 4 ) {
                case 0:
                    ASSERT_TRUE( s.insert( i ));
                    ASSERT_FALSE( s.insert( i ));
                    updResult = s.update( i, []( value_type& val, value_type* arg)
                        {
                            ASSERT_TRUE( arg != nullptr );
                            EXPECT_EQ( val.key(), arg->key());
                        }, false );
                    EXPECT_TRUE( updResult.first );
                    EXPECT_FALSE( updResult.second );
                    break;
                case 1:
                    EXPECT_EQ( i.nUpdateNewCount, 0u );
                    ASSERT_TRUE( s.insert( i, []( value_type& v ) { ++v.nUpdateNewCount;} ));
                    EXPECT_EQ( i.nUpdateNewCount, 1u );
                    ASSERT_FALSE( s.insert( i, []( value_type& v ) { ++v.nUpdateNewCount;} ));
                    EXPECT_EQ( i.nUpdateNewCount, 1u );
                    i.nUpdateNewCount = 0;
                    break;
                case 2:
                    updResult = s.update( i, []( value_type& /*val*/, value_type* arg )
                    {
                        EXPECT_TRUE( arg == nullptr );
                    });
                    EXPECT_TRUE( updResult.first );
                    EXPECT_TRUE( updResult.second );
                    break;
                case 3:
                    updResult = s.upsert( i );
                    EXPECT_TRUE( updResult.first );
                    EXPECT_TRUE( updResult.second );
                    break;
                }

                ASSERT_TRUE( s.contains( i.nKey ));
                ASSERT_TRUE( s.contains( i ));
                ASSERT_TRUE( s.contains( other_item( i.key()), other_less()));
                EXPECT_EQ( i.nFindCount, 0u );
                ASSERT_TRUE( s.find( i.nKey, []( value_type& v, int ) { ++v.nFindCount; } ));
                EXPECT_EQ( i.nFindCount, 1u );
                ASSERT_TRUE( s.find_with( other_item( i.key()), other_less(), []( value_type& v, other_item const& ) { ++v.nFindCount; } ));
                EXPECT_EQ( i.nFindCount, 2u );
                ASSERT_TRUE( s.find( i.nKey ) != s.end());
                ASSERT_TRUE( s.find_with( other_item( i.key()), other_less()) != s.end());
                EXPECT_EQ( s.find( i.nKey )->nKey, i.key());
                EXPECT_EQ( s.find_with( other_item( i.key()), other_less())->nKey, i.key());
            }
            ASSERT_FALSE( s.empty());
            ASSERT_CONTAINER_SIZE( s, nSetSize );

            std::for_each( data.begin(), data.end(), []( value_type& v ) { v.clear_stat(); });

            // erase
            shuffle( indices.begin(), indices.end());
            for ( auto idx : indices ) {
                auto& i = data[ idx ];

                ASSERT_TRUE( s.contains( i.nKey ));
                ASSERT_TRUE( s.contains( i ));
                ASSERT_TRUE( s.contains( other_item( i.key()), other_less()));
                EXPECT_EQ( i.nFindCount, 0u );
                ASSERT_TRUE( s.find( i.nKey, []( value_type& v, int ) { ++v.nFindCount; } ));
                EXPECT_EQ( i.nFindCount, 1u );
                ASSERT_TRUE( s.find_with( other_item( i.key()), other_less(), []( value_type& v, other_item const& ) { ++v.nFindCount; } ));
                EXPECT_EQ( i.nFindCount, 2u );
                ASSERT_TRUE( s.find( i.nKey ) != s.end());
                ASSERT_TRUE( s.find_with( other_item( i.key()), other_less()) != s.end());
                EXPECT_EQ( s.find( i.nKey )->nKey, i.key());
                EXPECT_EQ( s.find_with( other_item( i.key()), other_less())->nKey, i.key());


                value_type v( i );
                switch ( i.key() % 6 ) {
                case 0:
                    ASSERT_FALSE( s.unlink( v ));
                    ASSERT_TRUE( s.unlink( i ));
                    ASSERT_FALSE( s.unlink( i ));
                    break;
                case 1:
                    ASSERT_TRUE( s.erase( i.key()));
                    ASSERT_FALSE( s.erase( i.key()));
                    break;
                case 2:
                    ASSERT_TRUE( s.erase( v ));
                    ASSERT_FALSE( s.erase( v ));
                    break;
                case 3:
                    ASSERT_TRUE( s.erase_with( other_item( i.key()), other_less()));
                    ASSERT_FALSE( s.erase_with( other_item( i.key()), other_less()));
                    break;
                case 4:
                    EXPECT_EQ( i.nEraseCount, 0u );
                    ASSERT_TRUE( s.erase( v, []( value_type& val ) { ++val.nEraseCount; } ));
                    EXPECT_EQ( i.nEraseCount, 1u );
                    ASSERT_FALSE( s.erase( v, []( value_type& val ) { ++val.nEraseCount; } ));
                    EXPECT_EQ( i.nEraseCount, 1u );
                    break;
                case 5:
                    EXPECT_EQ( i.nEraseCount, 0u );
                    ASSERT_TRUE( s.erase_with( other_item( i.key()), other_less(), []( value_type& val ) { ++val.nEraseCount; } ));
                    EXPECT_EQ( i.nEraseCount, 1u );
                    ASSERT_FALSE( s.erase_with( other_item( i.key()), other_less(), []( value_type& val ) { ++val.nEraseCount; } ));
                    EXPECT_EQ( i.nEraseCount, 1u );
                    break;
                }

                ASSERT_FALSE( s.contains( i.nKey ));
                ASSERT_FALSE( s.contains( i ));
                ASSERT_FALSE( s.contains( other_item( i.key()), other_less()));
                ASSERT_FALSE( s.find( i.nKey, []( value_type&, int ) {} ));
                ASSERT_FALSE( s.find_with( other_item( i.key()), other_less(), []( value_type&, other_item const& ) {} ));
                ASSERT_TRUE( s.find( i.nKey ) == s.end());
                ASSERT_TRUE( s.find_with( other_item( i.key()), other_less()) == s.end());
            }
            ASSERT_TRUE( s.empty());
            ASSERT_CONTAINER_SIZE( s, 0u );

            // Force retiring cycle
            Set::gc::force_dispose();
            for ( auto& i : data ) {
                EXPECT_EQ( i.nDisposeCount, 1u );
            }

            // clear
            for ( auto& i : data ) {
                i.clear_stat();
                ASSERT_TRUE( s.insert( i ));
            }
            ASSERT_FALSE( s.empty());
            ASSERT_CONTAINER_SIZE( s, nSetSize );

            // Iterator test
            for ( auto it = s.begin(); it != s.end(); ++it ) {
                ++it->nFindCount;
            }
            for ( auto it = s.cbegin(); it != s.cend(); ++it ) {
                EXPECT_EQ( it->nFindCount, 1u );
            }
            for ( auto& i : data ) {
                EXPECT_EQ( i.nFindCount, 1u );
            }

            // erase_at() test
            for ( auto it = s.begin(); it != s.end(); ++it ) {
                EXPECT_TRUE( s.erase_at( it ));
                EXPECT_FALSE( s.erase_at( it ));
            }

            ASSERT_TRUE( s.empty());
            ASSERT_CONTAINER_SIZE( s, 0u );
            ASSERT_TRUE( s.begin() == s.end());
            ASSERT_TRUE( s.cbegin() == s.cend());

            // Force retiring cycle
            Set::gc::force_dispose();
            for ( auto& i : data ) {
                EXPECT_EQ( i.nDisposeCount, 1u );
            }

        }
    };

} // namespace cds_test

#endif // #ifndef CDSUNIT_SET_TEST_INTRUSIVE_SPLIT_ITERABLE_SET_H
