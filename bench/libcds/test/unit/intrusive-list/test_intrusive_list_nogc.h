// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)
#ifndef CDSUNIT_LIST_TEST_INTRUSIVE_LIST_NOGC_H
#define CDSUNIT_LIST_TEST_INTRUSIVE_LIST_NOGC_H

#include <cds_test/check_size.h>
#include <cds_test/fixture.h>

namespace cds_test {

    class intrusive_list_nogc : public fixture
    {
    public:
        struct stat {
            int nDisposeCount;
            int nUpdateExistsCall;
            int nUpdateNewCall;
            int nFindCall;

            stat()
                : nDisposeCount( 0 )
                , nUpdateExistsCall( 0 )
                , nUpdateNewCall( 0 )
                , nFindCall( 0 )
            {}

            stat( const stat& s )
            {
                *this = s;
            }

            stat& operator =( const stat& s )
            {
                memcpy( this, &s, sizeof( s ));
                return *this;
            }
        };

        template <typename Node>
        struct base_item : public Node
        {
            int nKey;
            int nVal;

            mutable stat    s;

            base_item()
            {}

            base_item( int key, int val )
                : nKey( key )
                , nVal( val )
                , s()
            {}

            base_item( const base_item& v )
                : nKey( v.nKey )
                , nVal( v.nVal )
                , s()
            {}

            const int& key() const
            {
                return nKey;
            }

            base_item& operator=( base_item const& src )
            {
                nKey = src.nKey;
                nVal = src.nVal;
                return *this;
            }

            base_item& operator=( base_item&& src )
            {
                nKey = src.nKey;
                nVal = src.nVal;
                return *this;
            }
        };

        template <typename Node>
        struct member_item
        {
            int nKey;
            int nVal;
            Node hMember;
            mutable stat s;

            member_item()
            {}

            member_item( int key, int val )
                : nKey( key )
                , nVal( val )
                , s()
            {}

            member_item( const member_item& v )
                : nKey( v.nKey )
                , nVal( v.nVal )
                , s()
            {}

            const int& key() const
            {
                return nKey;
            }

            member_item& operator =( member_item const& src )
            {
                nKey = src.nKey;
                nVal = src.nVal;
                return *this;
            }

            member_item& operator=( member_item&& src )
            {
                nKey = src.nKey;
                nVal = src.nVal;
                return *this;
            }
        };

        template <typename T>
        struct less
        {
            bool operator ()( const T& v1, const T& v2 ) const
            {
                return v1.key() < v2.key();
            }

            template <typename Q>
            bool operator ()( const T& v1, const Q& v2 ) const
            {
                return v1.key() < v2;
            }

            template <typename Q>
            bool operator ()( const Q& v1, const T& v2 ) const
            {
                return v1 < v2.key();
            }
        };

        struct other_item {
            int nKey;

            other_item( int n )
                : nKey( n )
            {}
        };

        struct other_less {
            template <typename T, typename Q>
            bool operator()( T const& i1, Q const& i2 ) const
            {
                return i1.nKey < i2.nKey;
            }
        };

        template <typename T>
        struct cmp {
            int operator ()( const T& v1, const T& v2 ) const
            {
                if ( v1.key() < v2.key())
                    return -1;
                return v1.key() > v2.key() ? 1 : 0;
            }

            template <typename Q>
            int operator ()( const T& v1, const Q& v2 ) const
            {
                if ( v1.key() < v2 )
                    return -1;
                return v1.key() > v2 ? 1 : 0;
            }

            template <typename Q>
            int operator ()( const Q& v1, const T& v2 ) const
            {
                if ( v1 < v2.key())
                    return -1;
                return v1 > v2.key() ? 1 : 0;
            }
        };

        struct mock_disposer
        {
            template <typename T>
            void operator ()( T * p )
            {
                ++p->s.nDisposeCount;
            }
        };

        struct mock_disposer2
        {
            template <typename T>
            void operator ()( T * p )
            {
                p->s.nDisposeCount += 10;
            }
        };

        struct update_functor
        {
            template <typename T>
            void operator ()( bool bNew, T& item, T& /*val*/ )
            {
                if ( bNew )
                    ++item.s.nUpdateNewCall;
                else
                    ++item.s.nUpdateExistsCall;
            }
        };

        struct find_functor
        {
            template <typename T, typename Q>
            void operator ()( T& item, Q& /*val*/ )
            {
                ++item.s.nFindCall;
            }
        };

        struct erase_functor
        {
            template <typename T>
            void operator()( T const& item )
            {
                item.s.nEraseCall++;
            }
        };

    protected:
        template <typename List>
        void test_common( List& l )
        {
            // Precondition: list is empty
            // Postcondition: list is empty

            static const size_t nSize = 20;
            typedef typename List::value_type value_type;
            value_type arr[ nSize ];

            for ( size_t i = 0; i < nSize; ++i ) {
                arr[i].nKey = static_cast<int>( i );
                arr[i].nVal = arr[i].nKey * 10;
            }
            shuffle( arr, arr + nSize );

            ASSERT_TRUE( l.empty());
            ASSERT_CONTAINER_SIZE( l, 0 );

            // insert / find
            for ( auto& i : arr ) {
                EXPECT_FALSE( l.contains( i.nKey ));
                EXPECT_FALSE( l.contains( other_item( i.nKey ), other_less()));
                EXPECT_FALSE( l.find( i.nKey, []( value_type& item, int ) { ++item.s.nFindCall; } ));
                EXPECT_EQ( i.s.nFindCall, 0 );
                EXPECT_FALSE( l.find_with( other_item( i.nKey ), other_less(), []( value_type& item, other_item const& ) { ++item.s.nFindCall; } ));
                EXPECT_EQ( i.s.nFindCall, 0 );

                EXPECT_TRUE( l.insert( i ));

                EXPECT_TRUE( l.contains( i.nKey ));
                EXPECT_TRUE( l.contains( i ));
                EXPECT_TRUE( l.contains( other_item( i.nKey ), other_less()));
                EXPECT_TRUE( l.find( i.nKey, []( value_type& item, int ) { ++item.s.nFindCall; } ));
                EXPECT_EQ( i.s.nFindCall, 1 );
                EXPECT_TRUE( l.find( i, []( value_type& item, value_type const& ) { ++item.s.nFindCall; } ));
                EXPECT_EQ( i.s.nFindCall, 2 );
                EXPECT_TRUE( l.find_with( other_item( i.nKey ), other_less(), []( value_type& item, other_item const& ) { ++item.s.nFindCall; } ));
                EXPECT_EQ( i.s.nFindCall, 3 );

                EXPECT_FALSE( l.insert( i ));
                ASSERT_FALSE( l.empty());
            }
            ASSERT_CONTAINER_SIZE( l, nSize );

            // check all items
            for ( auto const& i : arr ) {
                EXPECT_TRUE( l.contains( i.nKey ));
                EXPECT_TRUE( l.contains( i ));
                EXPECT_TRUE( l.contains( other_item( i.nKey ), other_less()));
                EXPECT_TRUE( l.find( i.nKey, []( value_type& item, int ) { ++item.s.nFindCall; } ));
                EXPECT_EQ( i.s.nFindCall, 4 );
                EXPECT_TRUE( l.find( i, []( value_type& item, value_type const& ) { ++item.s.nFindCall; } ));
                EXPECT_EQ( i.s.nFindCall, 5 );
                EXPECT_TRUE( l.find_with( other_item( i.nKey ), other_less(), []( value_type& item, other_item const& ) { ++item.s.nFindCall; } ));
                EXPECT_EQ( i.s.nFindCall, 6 );
            }
            ASSERT_FALSE( l.empty());
            ASSERT_CONTAINER_SIZE( l, nSize );

            // update existing test
            for ( auto& i : arr ) {
                EXPECT_EQ( i.s.nUpdateExistsCall, 0 );
                std::pair<bool, bool> ret = l.update( i, update_functor());
                EXPECT_TRUE( ret.first );
                EXPECT_FALSE( ret.second );
                EXPECT_EQ( i.s.nUpdateExistsCall, 1 );

                ret = l.update( i, []( bool bNew, value_type& vi, value_type& arg ) {
                    EXPECT_FALSE( bNew );
                    EXPECT_EQ( vi.s.nUpdateExistsCall, 1 );
                    EXPECT_TRUE( &vi == &arg );
                    ++vi.s.nUpdateExistsCall;
                });
                EXPECT_TRUE( ret.first );
                EXPECT_FALSE( ret.second );
                EXPECT_EQ( i.s.nUpdateExistsCall, 2 );
            }

            // clear() test
            l.clear();
            EXPECT_TRUE( l.empty());
            EXPECT_CONTAINER_SIZE( l, 0 );

            // Apply retired pointer to clean links
            List::gc::force_dispose();
            for ( auto const& i : arr ) {
                EXPECT_EQ( i.s.nDisposeCount, 1 );
                EXPECT_FALSE( l.contains( i ));
            }


            for ( auto& i : arr ) {
                std::pair<bool, bool> ret = l.update( i, update_functor(), false );
                EXPECT_FALSE( ret.first );
                EXPECT_FALSE( ret.second );

                ret = l.update( i, update_functor(), true );
                EXPECT_TRUE( ret.first );
                EXPECT_TRUE( ret.second );
                EXPECT_EQ( i.s.nUpdateNewCall, 1 );
            }

            EXPECT_FALSE( l.empty());
            EXPECT_CONTAINER_SIZE( l, nSize );

            l.clear( mock_disposer2());

            EXPECT_TRUE( l.empty());
            EXPECT_CONTAINER_SIZE( l, 0 );

            // Apply retired pointer to clean links
            List::gc::force_dispose();
            for ( auto const& i : arr ) {
                EXPECT_EQ( i.s.nDisposeCount, 11 );
                EXPECT_FALSE( l.contains( i ));
            }

            // Iterators on empty list
            {
                auto it = l.begin();
                auto itEnd = l.end();
                auto cit = l.cbegin();
                auto citEnd = l.cend();

                EXPECT_TRUE( it == itEnd );
                EXPECT_TRUE( it == cit );
                EXPECT_TRUE( cit == citEnd );

                ++it;
                ++cit;

                EXPECT_TRUE( it == itEnd );
                EXPECT_TRUE( it == cit );
                EXPECT_TRUE( cit == citEnd );
            }
        }

        template <typename List>
        void test_ordered_iterator( List& l )
        {
            // Precondition: list is empty
            // Postcondition: list is empty

            static const size_t nSize = 20;
            typedef typename List::value_type value_type;
            value_type arr[nSize];

            for ( size_t i = 0; i < nSize; ++i ) {
                arr[i].nKey = static_cast<int>(i);
                arr[i].nVal = arr[i].nKey * 10;
            }
            shuffle( arr, arr + nSize );

            ASSERT_TRUE( l.empty());
            ASSERT_CONTAINER_SIZE( l, 0 );

            for ( auto& i : arr )
                EXPECT_TRUE( l.insert( i ));

            int key = 0;
            for ( auto it = l.begin(); it != l.end(); ++it ) {
                EXPECT_EQ( it->nKey, key );
                EXPECT_EQ( (*it).nKey, key );
                ++key;
            }

            key = 0;
            for ( auto it = l.cbegin(); it != l.cend(); ++it ) {
                EXPECT_EQ( it->nKey, key );
                EXPECT_EQ( (*it).nKey, key );
                ++key;
            }

            l.clear();
            List::gc::force_dispose();
            for ( auto const& i : arr ) {
                EXPECT_EQ( i.s.nDisposeCount, 1 );
                EXPECT_FALSE( l.contains( i ));
            }
        }

        template <typename List>
        void test_unordered_iterator( List& l )
        {
            // Precondition: list is empty
            // Postcondition: list is empty

            static const size_t nSize = 20;
            typedef typename List::value_type value_type;
            value_type arr[nSize];

            for ( size_t i = 0; i < nSize; ++i ) {
                arr[i].nKey = static_cast<int>(i);
                arr[i].nVal = arr[i].nKey * 10;
            }
            shuffle( arr, arr + nSize );

            ASSERT_TRUE( l.empty());
            ASSERT_CONTAINER_SIZE( l, 0 );

            for ( auto& i : arr )
                EXPECT_TRUE( l.insert( i ));

            size_t idx = 0;
            for ( auto it = l.begin(); it != l.end(); ++it, ++idx ) {
                ASSERT_LT( idx, nSize );
                EXPECT_EQ( it->nKey, arr[idx].nKey );
                EXPECT_EQ( (*it).nKey, arr[idx].nKey );
            }

            idx = 0;
            for ( auto it = l.cbegin(); it != l.cend(); ++it, ++idx ) {
                ASSERT_LT( idx, nSize );
                EXPECT_EQ( it->nKey, arr[idx].nKey );
                EXPECT_EQ( (*it).nKey, arr[idx].nKey );
            }

            l.clear();
            List::gc::force_dispose();
            for ( auto const& i : arr ) {
                EXPECT_EQ( i.s.nDisposeCount, 1 );
                EXPECT_FALSE( l.contains( i ));
            }
        }
    };

} // namespace cds_test

#endif // CDSUNIT_LIST_TEST_INTRUSIVE_LIST_NOGC_H
