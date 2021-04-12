// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef CDSUNIT_MAP_TYPE_H
#define CDSUNIT_MAP_TYPE_H

#include <cds/urcu/general_instant.h>
#include <cds/urcu/general_buffered.h>
#include <cds/urcu/general_threaded.h>
#include <cds/urcu/signal_buffered.h>

#include <cds/sync/spinlock.h>
#include <cds/opt/hash.h>
#include <boost/functional/hash/hash.hpp>

#include <cds_test/stress_test.h>
#include <cds_test/check_size.h>

namespace map {
    namespace cc = cds::container;
    namespace co = cds::opt;

    typedef cds::urcu::gc< cds::urcu::general_instant_stripped >   rcu_gpi;
    typedef cds::urcu::gc< cds::urcu::general_buffered_stripped >  rcu_gpb;
    typedef cds::urcu::gc< cds::urcu::general_threaded_stripped >  rcu_gpt;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
    typedef cds::urcu::gc< cds::urcu::signal_buffered_stripped >  rcu_shb;
#endif

    template <typename Key>
    struct less;

    template <typename Key>
    struct cmp {
        int operator ()(Key const& k1, Key const& k2) const
        {
            if ( less<Key>( k1, k2 ))
                return -1;
            return less<Key>( k2, k1 ) ? 1 : 0;
        }
    };

    template <typename Key>
    struct hash;

#define CDSUNIT_INT_COMPARE(t)  template <> struct cmp<t> { int operator()( t k1, t k2 ) const { return (int)(k1 - k2); } }
    CDSUNIT_INT_COMPARE(char);
    CDSUNIT_INT_COMPARE(unsigned char);
    CDSUNIT_INT_COMPARE(int);
    CDSUNIT_INT_COMPARE(unsigned int);
    CDSUNIT_INT_COMPARE(long);
    CDSUNIT_INT_COMPARE(unsigned long);
    CDSUNIT_INT_COMPARE(long long);
    CDSUNIT_INT_COMPARE(unsigned long long);
#undef CDSUNIT_INT_COMPARE

#define CDSUNIT_INT_LESS(t)  template <> struct less<t> { bool operator()( t k1, t k2 ) const { return k1 < k2; } }
    CDSUNIT_INT_LESS( char );
    CDSUNIT_INT_LESS( unsigned char );
    CDSUNIT_INT_LESS( int );
    CDSUNIT_INT_LESS( unsigned int );
    CDSUNIT_INT_LESS( long );
    CDSUNIT_INT_LESS( unsigned long );
    CDSUNIT_INT_LESS( long long );
    CDSUNIT_INT_LESS( unsigned long long );
#undef CDSUNIT_INT_LESS

    template <>
    struct cmp<std::string>
    {
        int operator()(std::string const& s1, std::string const& s2)
        {
            return s1.compare( s2 );
        }
        int operator()(std::string const& s1, char const * s2)
        {
            return s1.compare( s2 );
        }
        int operator()(char const * s1, std::string const& s2)
        {
            return -s2.compare( s1 );
        }
    };

    template <>
    struct less<std::string>
    {
        bool operator ()( std::string const& k1, std::string const& k2 ) const
        {
            return cmp<std::string>()(k1, k2) < 0;
        }
        bool operator ()( std::string const& k1, char const* k2 ) const
        {
            return cmp<std::string>()(k1, k2) < 0;
        }
        bool operator ()( char const* k1, std::string const& k2 ) const
        {
            return cmp<std::string>()(k1, k2) < 0;
        }
    };

    template <typename T>
    struct hash
    {
        typedef size_t result_type;
        typedef T      argument_type;

        size_t operator()( T const& k ) const
        {
            return std::hash<size_t>()(k.nKey);
        }

        size_t operator()( size_t k ) const
        {
            return std::hash<size_t>()(k);
        }
    };

    template <>
    struct hash<size_t>
    {
        typedef size_t result_type;
        typedef size_t argument_type;

        size_t operator()( size_t k ) const
        {
            return std::hash<size_t>()(k);
        }
    };

    template <>
    struct hash<std::string>
    {
        typedef size_t result_type;
        typedef std::string argument_type;

        size_t operator()( std::string const& k ) const
        {
            return std::hash<std::string>()(k);
        }
    };

    // forward
    template <typename ImplSelector, typename Key, typename Value>
    struct map_type;

    template <typename Key, typename Value>
    struct map_type_base
    {
        typedef map::hash<Key>    key_hash;
        typedef map::less<Key>    key_less;
        typedef cmp<Key>          key_compare;

        struct equal_to {
            bool operator()( Key const& k1, Key const& k2 ) const
            {
                return key_compare()( k1, k2 ) == 0;
            }
        };

        struct hash2: public key_hash
        {
            size_t operator()( Key const& k ) const
            {
                size_t h = key_hash::operator ()( k );
                size_t seed = ~h;
                seed ^= h + 0x9e3779b9 + (seed << 6) + (seed >> 2);
                return seed;
            }
            template <typename Q>
            size_t operator()( Q const& k ) const
            {
                size_t h = key_hash::operator ()( k );
                size_t seed = ~h;
                seed ^= h + 0x9e3779b9 + (seed << 6) + (seed >> 2);
                return seed;
            }
        };
    };

    struct empty_stat {};
    static inline cds_test::property_stream& operator <<( cds_test::property_stream& o, empty_stat const& )
    {
        return o;
    }

    template <typename Map>
    static inline void print_stat( cds_test::property_stream& o, Map const& m )
    {
        o << m.statistics();
    }


    template <typename Map>
    static inline void check_before_cleanup( Map& /*m*/ )
    {}

    template <typename Map>
    static inline void additional_cleanup( Map& /*m*/ )
    {}

    template <typename Map>
    static inline void additional_check( Map& /*m*/ )
    {}

} // namespace map

#endif // ifndef CDSUNIT_MAP_TYPE_H
