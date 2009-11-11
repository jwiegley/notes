#if defined(HAVE_BOOST_SERIALIZATION)

namespace boost {
namespace serialization {

template <class Archive>
void serialize(Archive& ar, MP_RAT& mpq, const unsigned int /* version */)
{
  ar & mpq._mp_num;
  ar & mpq._mp_den;
}

} // namespace serialization
} // namespace boost

template void boost::serialization::serialize(boost::archive::binary_iarchive&,
                                              MP_RAT&, const unsigned int);

#endif // HAVE_BOOST_SERIALIZATION
