// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef CDSUNIT_SET_TEST_TREE_SET_H
#define CDSUNIT_SET_TEST_TREE_SET_H

#include <cds_test/check_size.h>
#include <cds_test/fixture.h>

// forward declaration
namespace cds { namespace container {}}

namespace cds_test {

    class container_tree_set : public fixture
    {
    public:
        static size_t const kSize = 1000;

        struct stat
        {
            unsigned int nFindCount;
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

        struct int_item: public stat
        {
            int nKey;
            int nVal;
            std::string strVal;

            int_item()
                : nKey( 0 )
                , nVal( 0 )
            {}

            explicit int_item( int k )
                : nKey( k )
                , nVal( k * 2 )
            {}

            template <typename Q>
            explicit int_item( Q const& src )
                : nKey( src.key())
                , nVal( 0 )
            {}

            int_item( int_item const& src )
                : nKey( src.nKey )
                , nVal( src.nVal )
                , strVal( src.strVal )
            {}

            int_item( int_item&& src )
                : nKey( src.nKey )
                , nVal( src.nVal )
                , strVal( std::move( src.strVal ))
            {}

            int_item( int k, std::string&& s )
                : nKey( k )
                , nVal( k * 2 )
                , strVal( std::move( s ))
            {}

            explicit int_item( other_item const& s )
                : nKey( s.key())
                , nVal( s.key() * 2 )
            {}

            int key() const
            {
                return nKey;
            }
        };

        struct key_extractor
        {
            template <typename T>
            void operator()( int& key, T const& val ) const
            {
                key = val.key();
            }
        };

        struct simple_item_counter {
            size_t  m_nCount;

            simple_item_counter()
                : m_nCount( 0 )
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

        struct less
        {
            bool operator ()( int_item const& v1, int_item const& v2 ) const
            {
                return v1.key() < v2.key();
            }

            bool operator()( int lhs, int rhs ) const
            {
                return lhs < rhs;
            }

            template <typename Q>
            bool operator ()( int_item const& v1, const Q& v2 ) const
            {
                return v1.key() < v2;
            }

            template <typename Q>
            bool operator ()( const Q& v1, int_item const& v2 ) const
            {
                return v1 < v2.key();
            }
        };

        struct cmp {
            int operator ()( int_item const& v1, int_item const& v2 ) const
            {
                if ( v1.key() < v2.key())
                    return -1;
                return v1.key() > v2.key() ? 1 : 0;
            }

            int operator()( int lhs, int rhs ) const
            {
                return lhs - rhs;
            }

            template <typename T>
            int operator ()( T const& v1, int v2 ) const
            {
                if ( v1.key() < v2 )
                    return -1;
                return v1.key() > v2 ? 1 : 0;
            }

            template <typename T>
            int operator ()( int v1, T const& v2 ) const
            {
                if ( v1 < v2.key())
                    return -1;
                return v1 > v2.key() ? 1 : 0;
            }
        };

        struct other_less {
            template <typename Q, typename T>
            bool operator()( Q const& lhs, T const& rhs ) const
            {
                return lhs.key() < rhs.key();
            }

            bool operator()( int lhs, other_item const& rhs ) const
            {
                return lhs < rhs.key();
            }

            bool operator()( other_item const& lhs, int rhs ) const
            {
                return lhs.key() < rhs;
            }
        };

    protected:
        template <typename Set>
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
                data.push_back( value_type( static_cast<int>(key)));
                indices.push_back( key );
            }
            shuffle( indices.begin(), indices.end());

            // insert/find
            for ( auto idx : indices ) {
                auto& i = data[idx];

                ASSERT_FALSE( s.contains( i.nKey ));
                ASSERT_FALSE( s.contains( i ));
                ASSERT_FALSE( s.contains( other_item( i.key()), other_less()));
                ASSERT_FALSE( s.find( i.nKey, []( value_type&, int ) {} ));
                ASSERT_FALSE( s.find( i, []( value_type&, value_type const& ) {} ));
                ASSERT_FALSE( s.find_with( other_item( i.key()), other_less(), []( value_type&, other_item const& ) {} ));

                std::pair<bool, bool> updResult;

                std::string str;
                updResult = s.update( i.key(), []( bool, value_type&, int )
                {
                    ASSERT_TRUE( false );
                }, false );
                EXPECT_FALSE( updResult.first );
                EXPECT_FALSE( updResult.second );

                switch ( idx % 8 ) {
                case 0:
                    ASSERT_TRUE( s.insert( i ));
                    ASSERT_FALSE( s.insert( i ));
                    updResult = s.update( i, []( bool bNew, value_type& val, value_type const& arg)
                        {
                            EXPECT_FALSE( bNew );
                            EXPECT_EQ( val.key(), arg.key());
                        }, false );
                    EXPECT_TRUE( updResult.first );
                    EXPECT_FALSE( updResult.second );
                    break;
                case 1:
                    ASSERT_TRUE( s.insert( i.key()));
                    ASSERT_FALSE( s.insert( i.key()));
                    updResult = s.update( i.key(), []( bool bNew, value_type& val, int arg)
                        {
                            EXPECT_FALSE( bNew );
                            EXPECT_EQ( val.key(), arg );
                        }, false );
                    EXPECT_TRUE( updResult.first );
                    EXPECT_FALSE( updResult.second );
                    break;
                case 2:
                    ASSERT_TRUE( s.insert( i, []( value_type& v ) { ++v.nFindCount; } ));
                    ASSERT_FALSE( s.insert( i, []( value_type& v ) { ++v.nFindCount; } ));
                    ASSERT_TRUE( s.find( i.nKey, []( value_type const& v, int key )
                        {
                            EXPECT_EQ( v.key(), key );
                            EXPECT_EQ( v.nFindCount, 1u );
                        }));
                    break;
                case 3:
                    ASSERT_TRUE( s.insert( i.key(), []( value_type& v ) { ++v.nFindCount; } ));
                    ASSERT_FALSE( s.insert( i.key(), []( value_type& v ) { ++v.nFindCount; } ));
                    ASSERT_TRUE( s.find( i.nKey, []( value_type const& v, int key )
                        {
                            EXPECT_EQ( v.key(), key );
                            EXPECT_EQ( v.nFindCount, 1u );
                        }));
                    break;
                case 4:
                    updResult = s.update( i, []( bool bNew, value_type& v, value_type const& arg )
                        {
                            EXPECT_TRUE( bNew );
                            EXPECT_EQ( v.key(), arg.key());
                            ++v.nUpdateNewCount;
                        });
                    EXPECT_TRUE( updResult.first );
                    EXPECT_TRUE( updResult.second );

                    updResult = s.update( i, []( bool bNew, value_type& v, value_type const& arg )
                        {
                            EXPECT_FALSE( bNew );
                            EXPECT_EQ( v.key(), arg.key());
                            ++v.nUpdateNewCount;
                        }, false );
                    EXPECT_TRUE( updResult.first );
                    EXPECT_FALSE( updResult.second );

                    ASSERT_TRUE( s.find( i.nKey, []( value_type const& v, int key )
                        {
                            EXPECT_EQ( v.key(), key );
                            EXPECT_EQ( v.nUpdateNewCount, 2u );
                        }));
                    break;
                case 5:
                    updResult = s.update( i.key(), []( bool bNew, value_type& v, int arg )
                        {
                            EXPECT_TRUE( bNew );
                            EXPECT_EQ( v.key(), arg );
                            ++v.nUpdateNewCount;
                        });
                    EXPECT_TRUE( updResult.first );
                    EXPECT_TRUE( updResult.second );

                    updResult = s.update( i.key(), []( bool bNew, value_type& v, int arg )
                        {
                            EXPECT_FALSE( bNew );
                            EXPECT_EQ( v.key(), arg );
                            ++v.nUpdateNewCount;
                        }, false );
                    EXPECT_TRUE( updResult.first );
                    EXPECT_FALSE( updResult.second );

                    ASSERT_TRUE( s.find( i, []( value_type const& v, value_type const& arg )
                        {
                            EXPECT_EQ( v.key(), arg.key());
                            EXPECT_EQ( v.nUpdateNewCount, 2u );
                        }));
                    break;
                case 6:
                    ASSERT_TRUE( s.emplace( i.key()));
                    ASSERT_TRUE( s.find( i, []( value_type const& v, value_type const& arg )
                        {
                            EXPECT_EQ( v.key(), arg.key());
                            EXPECT_EQ( v.nVal, arg.nVal );
                        }));
                    break;
                case 7:
                    str = "Hello!";
                    ASSERT_TRUE( s.emplace( i.key(), std::move( str )));
                    EXPECT_TRUE( str.empty());
                    ASSERT_TRUE( s.find( i, []( value_type const& v, value_type const& arg )
                        {
                            EXPECT_EQ( v.key(), arg.key());
                            EXPECT_EQ( v.nVal, arg.nVal );
                            EXPECT_EQ( v.strVal, std::string( "Hello!" ));
                        } ));
                    break;
                default:
                    // forgot anything?..
                    ASSERT_TRUE( false );
                }

                ASSERT_TRUE( s.contains( i.nKey ));
                ASSERT_TRUE( s.contains( i ));
                ASSERT_TRUE( s.contains( other_item( i.key()), other_less()));
                ASSERT_TRUE( s.find( i.nKey, []( value_type&, int ) {} ));
                ASSERT_TRUE( s.find( i, []( value_type&, value_type const& ) {} ));
                ASSERT_TRUE( s.find_with( other_item( i.key()), other_less(), []( value_type&, other_item const& ) {} ));
            }

            ASSERT_FALSE( s.empty());
            ASSERT_CONTAINER_SIZE( s, nSetSize );

            ASSERT_TRUE( s.check_consistency());

            // erase
            shuffle( indices.begin(), indices.end());
            for ( auto idx : indices ) {
                auto& i = data[idx];

                ASSERT_TRUE( s.contains( i.nKey ));
                ASSERT_TRUE( s.contains( i ));
                ASSERT_TRUE( s.contains( other_item( i.key()), other_less()));
                ASSERT_TRUE( s.find( i.nKey, []( value_type& v, int )
                    {
                        v.nFindCount = 1;
                    }));
                ASSERT_TRUE( s.find( i, []( value_type& v, value_type const& )
                    {
                        EXPECT_EQ( ++v.nFindCount, 2u );
                    }));
                ASSERT_TRUE( s.find_with( other_item( i.key()), other_less(), []( value_type& v, other_item const& )
                    {
                        EXPECT_EQ( ++v.nFindCount, 3u );
                    }));

                int nKey = i.key() - 1;
                switch ( idx % 6 ) {
                case 0:
                    ASSERT_TRUE( s.erase( i.key()));
                    ASSERT_FALSE( s.erase( i.key()));
                    break;
                case 1:
                    ASSERT_TRUE( s.erase( i ));
                    ASSERT_FALSE( s.erase( i ));
                    break;
                case 2:
                    ASSERT_TRUE( s.erase_with( other_item( i.key()), other_less()));
                    ASSERT_FALSE( s.erase_with( other_item( i.key()), other_less()));
                    break;
                case 3:
                    ASSERT_TRUE( s.erase( i.key(), [&nKey]( value_type const& v )
                        {
                            nKey = v.key();
                        } ));
                    EXPECT_EQ( i.key(), nKey );

                    nKey = i.key() - 1;
                    ASSERT_FALSE( s.erase( i.key(), [&nKey]( value_type const& v )
                        {
                            nKey = v.key();
                        } ));
                    EXPECT_EQ( i.key(), nKey + 1 );
                    break;
                case 4:
                    ASSERT_TRUE( s.erase( i, [&nKey]( value_type const& v )
                        {
                            nKey = v.key();
                        } ));
                    EXPECT_EQ( i.key(), nKey );

                    nKey = i.key() - 1;
                    ASSERT_FALSE( s.erase( i, [&nKey]( value_type const& v )
                        {
                            nKey = v.key();
                        } ));
                    EXPECT_EQ( i.key(), nKey + 1 );
                    break;
                case 5:
                    ASSERT_TRUE( s.erase_with( other_item( i.key()), other_less(), [&nKey]( value_type const& v )
                        {
                            nKey = v.key();
                        } ));
                    EXPECT_EQ( i.key(), nKey );

                    nKey = i.key() - 1;
                    ASSERT_FALSE( s.erase_with( other_item( i.key()), other_less(), [&nKey]( value_type const& v )
                        {
                            nKey = v.key();
                        } ));
                    EXPECT_EQ( i.key(), nKey + 1 );
                    break;
                }

                ASSERT_FALSE( s.contains( i.nKey ));
                ASSERT_FALSE( s.contains( i ));
                ASSERT_FALSE( s.contains( other_item( i.key()), other_less()));
                ASSERT_FALSE( s.find( i.nKey, []( value_type&, int ) {} ));
                ASSERT_FALSE( s.find( i, []( value_type&, value_type const& ) {} ));
                ASSERT_FALSE( s.find_with( other_item( i.key()), other_less(), []( value_type&, other_item const& ) {} ));
            }
            ASSERT_TRUE( s.empty());
            ASSERT_CONTAINER_SIZE( s, 0 );


            // clear
            for ( auto& i : data ) {
                ASSERT_TRUE( s.insert( i ));
            }

            ASSERT_FALSE( s.empty());
            ASSERT_CONTAINER_SIZE( s, nSetSize );

            s.clear();

            ASSERT_TRUE( s.empty());
            ASSERT_CONTAINER_SIZE( s, 0 );
        }
    };

} // namespace cds_test

#endif // CDSUNIT_SET_TEST_TREE_SET_H
